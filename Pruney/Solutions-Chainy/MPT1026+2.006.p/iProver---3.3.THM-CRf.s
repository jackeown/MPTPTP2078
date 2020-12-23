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

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  208 (4450 expanded)
%              Number of clauses        :  131 (1568 expanded)
%              Number of leaves         :   24 (1103 expanded)
%              Depth                    :   29
%              Number of atoms          :  735 (26674 expanded)
%              Number of equality atoms :  275 (7884 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f50,plain,
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

fof(f51,plain,
    ( ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      | ~ v1_funct_2(sK7,sK5,sK6)
      | ~ v1_funct_1(sK7) )
    & r2_hidden(sK7,k1_funct_2(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f33,f50])).

fof(f88,plain,(
    r2_hidden(sK7,k1_funct_2(sK5,sK6)) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f34,plain,(
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

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f13,f34])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f95,plain,(
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
    inference(nnf_transformation,[],[f34])).

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
     => ( r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0)
        & k1_relat_1(sK4(X0,X1,X6)) = X1
        & sK4(X0,X1,X6) = X6
        & v1_funct_1(sK4(X0,X1,X6))
        & v1_relat_1(sK4(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f44,f47,f46,f45])).

fof(f73,plain,(
    ! [X6,X2,X0,X1] :
      ( sK4(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK4(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f70,plain,(
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

fof(f86,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f89,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_2(sK7,sK5,sK6)
    | ~ v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK4(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK4(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_37,negated_conjecture,
    ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_5175,plain,
    ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_32,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_5177,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK4(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_5181,plain,
    ( sK4(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6961,plain,
    ( sK4(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5177,c_5181])).

cnf(c_7175,plain,
    ( sK4(sK6,sK5,sK7) = sK7 ),
    inference(superposition,[status(thm)],[c_5175,c_6961])).

cnf(c_26,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_5183,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7749,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(sK4(X2,X1,X0)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5177,c_5183])).

cnf(c_10602,plain,
    ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) != iProver_top
    | r1_tarski(k2_relat_1(sK7),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_7175,c_7749])).

cnf(c_38,plain,
    ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_11074,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10602,c_38])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_5197,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11080,plain,
    ( r1_tarski(k2_relat_1(sK7),X0) = iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11074,c_5197])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_5196,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_5191,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_27,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK4(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_5182,plain,
    ( k1_relat_1(sK4(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7052,plain,
    ( k1_relat_1(sK4(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5177,c_5182])).

cnf(c_7581,plain,
    ( k1_relat_1(sK4(sK6,sK5,sK7)) = sK5 ),
    inference(superposition,[status(thm)],[c_5175,c_7052])).

cnf(c_7583,plain,
    ( k1_relat_1(sK7) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_7581,c_7175])).

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

cnf(c_522,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | k2_relat_1(X3) != X2
    | k1_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_34])).

cnf(c_523,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_33,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_527,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_33])).

cnf(c_14,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_36,negated_conjecture,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_546,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK7)
    | sK6 != X2
    | sK5 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_36])).

cnf(c_547,plain,
    ( ~ v1_partfun1(sK7,sK5)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_611,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0))
    | k1_relat_1(X0) != sK5
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_527,c_547])).

cnf(c_612,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | v1_xboole_0(k2_relat_1(sK7))
    | k1_relat_1(sK7) != sK5 ),
    inference(unflattening,[status(thm)],[c_611])).

cnf(c_5170,plain,
    ( k1_relat_1(sK7) != sK5
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_7593,plain,
    ( sK5 != sK5
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7583,c_5170])).

cnf(c_7604,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7593])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_121,plain,
    ( r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_125,plain,
    ( ~ r1_tarski(sK7,sK7)
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_613,plain,
    ( k1_relat_1(sK7) != sK5
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_29,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK4(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_5496,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK5,sK6))
    | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
    | v1_funct_1(sK4(X0,X1,sK7)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_5604,plain,
    ( ~ sP0(sK6,sK5,k1_funct_2(sK5,sK6))
    | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
    | v1_funct_1(sK4(sK6,sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_5496])).

cnf(c_5606,plain,
    ( sP0(sK6,sK5,k1_funct_2(sK5,sK6)) != iProver_top
    | r2_hidden(sK7,k1_funct_2(sK5,sK6)) != iProver_top
    | v1_funct_1(sK4(sK6,sK5,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5604])).

cnf(c_5605,plain,
    ( sP0(sK6,sK5,k1_funct_2(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_5608,plain,
    ( sP0(sK6,sK5,k1_funct_2(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5605])).

cnf(c_4401,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5723,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK4(sK6,sK5,sK7))
    | X0 != sK4(sK6,sK5,sK7) ),
    inference(instantiation,[status(thm)],[c_4401])).

cnf(c_5724,plain,
    ( X0 != sK4(sK6,sK5,sK7)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK4(sK6,sK5,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5723])).

cnf(c_5726,plain,
    ( sK7 != sK4(sK6,sK5,sK7)
    | v1_funct_1(sK4(sK6,sK5,sK7)) != iProver_top
    | v1_funct_1(sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5724])).

cnf(c_30,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK4(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_5501,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK5,sK6))
    | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
    | v1_relat_1(sK4(X0,X1,sK7)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_5766,plain,
    ( ~ sP0(sK6,sK5,k1_funct_2(sK5,sK6))
    | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
    | v1_relat_1(sK4(sK6,sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_5501])).

cnf(c_5768,plain,
    ( sP0(sK6,sK5,k1_funct_2(sK5,sK6)) != iProver_top
    | r2_hidden(sK7,k1_funct_2(sK5,sK6)) != iProver_top
    | v1_relat_1(sK4(sK6,sK5,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5766])).

cnf(c_5532,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK5,sK6))
    | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
    | sK4(X0,X1,sK7) = sK7 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_5765,plain,
    ( ~ sP0(sK6,sK5,k1_funct_2(sK5,sK6))
    | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
    | sK4(sK6,sK5,sK7) = sK7 ),
    inference(instantiation,[status(thm)],[c_5532])).

cnf(c_4400,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5826,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK4(sK6,sK5,sK7))
    | X0 != sK4(sK6,sK5,sK7) ),
    inference(instantiation,[status(thm)],[c_4400])).

cnf(c_5832,plain,
    ( X0 != sK4(sK6,sK5,sK7)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK4(sK6,sK5,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5826])).

cnf(c_5834,plain,
    ( sK7 != sK4(sK6,sK5,sK7)
    | v1_relat_1(sK4(sK6,sK5,sK7)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5832])).

cnf(c_4391,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5948,plain,
    ( X0 != X1
    | X0 = sK4(sK6,sK5,sK7)
    | sK4(sK6,sK5,sK7) != X1 ),
    inference(instantiation,[status(thm)],[c_4391])).

cnf(c_5949,plain,
    ( sK4(sK6,sK5,sK7) != sK7
    | sK7 = sK4(sK6,sK5,sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_5948])).

cnf(c_8978,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7604,c_37,c_38,c_121,c_125,c_613,c_5606,c_5605,c_5608,c_5726,c_5768,c_5765,c_5834,c_5949,c_7583])).

cnf(c_9271,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | r1_tarski(k1_relat_1(sK7),sK5) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5191,c_8978])).

cnf(c_9298,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | r1_tarski(sK5,sK5) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9271,c_7583])).

cnf(c_9463,plain,
    ( r1_tarski(sK5,sK5) != iProver_top
    | r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9298,c_37,c_38,c_121,c_125,c_5605,c_5608,c_5768,c_5765,c_5834,c_5949])).

cnf(c_9464,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | r1_tarski(sK5,sK5) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_9463])).

cnf(c_5198,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9470,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9464,c_5198])).

cnf(c_11085,plain,
    ( v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11074,c_9470])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_5201,plain,
    ( r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_284,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_285,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_284])).

cnf(c_348,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_285])).

cnf(c_5174,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_5572,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5198,c_5174])).

cnf(c_5910,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5201,c_5572])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5192,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6149,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5196,c_5192])).

cnf(c_6259,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5910,c_6149])).

cnf(c_11229,plain,
    ( k1_relset_1(X0,X1,k2_relat_1(sK7)) = k1_relat_1(k2_relat_1(sK7)) ),
    inference(superposition,[status(thm)],[c_11085,c_6259])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_5193,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12866,plain,
    ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k1_relat_1(k2_relat_1(sK7)),k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11229,c_5193])).

cnf(c_16981,plain,
    ( m1_subset_1(k1_relat_1(k2_relat_1(sK7)),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(k2_relat_1(sK7),k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5196,c_12866])).

cnf(c_17117,plain,
    ( m1_subset_1(k1_relat_1(k2_relat_1(sK7)),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(sK6,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11080,c_16981])).

cnf(c_17114,plain,
    ( m1_subset_1(k1_relat_1(k2_relat_1(sK7)),k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5910,c_16981])).

cnf(c_17653,plain,
    ( m1_subset_1(k1_relat_1(k2_relat_1(sK7)),k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17117,c_38,c_9470,c_10602,c_17114])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_5195,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_17660,plain,
    ( r1_tarski(k1_relat_1(k2_relat_1(sK7)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17653,c_5195])).

cnf(c_5176,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_7615,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(sK7)))) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7583,c_5176])).

cnf(c_8229,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(sK7)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7615,c_37,c_38,c_121,c_125,c_5606,c_5605,c_5608,c_5726,c_5768,c_5765,c_5834,c_5949])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_5194,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8235,plain,
    ( v1_xboole_0(k2_relat_1(sK7)) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_8229,c_5194])).

cnf(c_11231,plain,
    ( v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_11085,c_8235])).

cnf(c_5199,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6191,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5910,c_5199])).

cnf(c_6472,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5910,c_6191])).

cnf(c_11228,plain,
    ( k2_relat_1(sK7) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11085,c_6472])).

cnf(c_12884,plain,
    ( k2_relat_1(sK7) = sK7 ),
    inference(superposition,[status(thm)],[c_11231,c_11228])).

cnf(c_18867,plain,
    ( r1_tarski(sK5,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17660,c_7583,c_12884])).

cnf(c_6927,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5196,c_5194])).

cnf(c_18877,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_18867,c_6927])).

cnf(c_18917,plain,
    ( v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_18877])).

cnf(c_16,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_593,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7)
    | ~ v1_xboole_0(X1)
    | sK5 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_547])).

cnf(c_594,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7)
    | ~ v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_4388,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7)
    | ~ v1_xboole_0(sK5)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_594])).

cnf(c_5171,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(sK5) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4388])).

cnf(c_4387,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_594])).

cnf(c_5172,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4387])).

cnf(c_5329,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5171,c_5172])).

cnf(c_9272,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | r1_tarski(k1_relat_1(sK7),sK5) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5191,c_5329])).

cnf(c_9288,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | r1_tarski(sK5,sK5) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9272,c_7583])).

cnf(c_5744,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK5,sK6)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5196,c_5329])).

cnf(c_6003,plain,
    ( v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(sK5) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5910,c_5744])).

cnf(c_9475,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9288,c_37,c_38,c_121,c_125,c_5606,c_5605,c_5608,c_5726,c_5765,c_5949,c_6003,c_8235,c_9470])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18917,c_10602,c_9475,c_9470,c_8235,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:56:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.75/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/0.97  
% 3.75/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.75/0.97  
% 3.75/0.97  ------  iProver source info
% 3.75/0.97  
% 3.75/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.75/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.75/0.97  git: non_committed_changes: false
% 3.75/0.97  git: last_make_outside_of_git: false
% 3.75/0.97  
% 3.75/0.97  ------ 
% 3.75/0.97  
% 3.75/0.97  ------ Input Options
% 3.75/0.97  
% 3.75/0.97  --out_options                           all
% 3.75/0.97  --tptp_safe_out                         true
% 3.75/0.97  --problem_path                          ""
% 3.75/0.97  --include_path                          ""
% 3.75/0.97  --clausifier                            res/vclausify_rel
% 3.75/0.97  --clausifier_options                    --mode clausify
% 3.75/0.97  --stdin                                 false
% 3.75/0.97  --stats_out                             all
% 3.75/0.97  
% 3.75/0.97  ------ General Options
% 3.75/0.97  
% 3.75/0.97  --fof                                   false
% 3.75/0.97  --time_out_real                         305.
% 3.75/0.97  --time_out_virtual                      -1.
% 3.75/0.97  --symbol_type_check                     false
% 3.75/0.97  --clausify_out                          false
% 3.75/0.97  --sig_cnt_out                           false
% 3.75/0.97  --trig_cnt_out                          false
% 3.75/0.97  --trig_cnt_out_tolerance                1.
% 3.75/0.97  --trig_cnt_out_sk_spl                   false
% 3.75/0.97  --abstr_cl_out                          false
% 3.75/0.97  
% 3.75/0.97  ------ Global Options
% 3.75/0.97  
% 3.75/0.97  --schedule                              default
% 3.75/0.97  --add_important_lit                     false
% 3.75/0.97  --prop_solver_per_cl                    1000
% 3.75/0.97  --min_unsat_core                        false
% 3.75/0.97  --soft_assumptions                      false
% 3.75/0.97  --soft_lemma_size                       3
% 3.75/0.97  --prop_impl_unit_size                   0
% 3.75/0.97  --prop_impl_unit                        []
% 3.75/0.97  --share_sel_clauses                     true
% 3.75/0.97  --reset_solvers                         false
% 3.75/0.97  --bc_imp_inh                            [conj_cone]
% 3.75/0.97  --conj_cone_tolerance                   3.
% 3.75/0.97  --extra_neg_conj                        none
% 3.75/0.97  --large_theory_mode                     true
% 3.75/0.97  --prolific_symb_bound                   200
% 3.75/0.97  --lt_threshold                          2000
% 3.75/0.97  --clause_weak_htbl                      true
% 3.75/0.97  --gc_record_bc_elim                     false
% 3.75/0.97  
% 3.75/0.97  ------ Preprocessing Options
% 3.75/0.97  
% 3.75/0.97  --preprocessing_flag                    true
% 3.75/0.97  --time_out_prep_mult                    0.1
% 3.75/0.97  --splitting_mode                        input
% 3.75/0.97  --splitting_grd                         true
% 3.75/0.97  --splitting_cvd                         false
% 3.75/0.97  --splitting_cvd_svl                     false
% 3.75/0.97  --splitting_nvd                         32
% 3.75/0.97  --sub_typing                            true
% 3.75/0.97  --prep_gs_sim                           true
% 3.75/0.97  --prep_unflatten                        true
% 3.75/0.97  --prep_res_sim                          true
% 3.75/0.97  --prep_upred                            true
% 3.75/0.97  --prep_sem_filter                       exhaustive
% 3.75/0.97  --prep_sem_filter_out                   false
% 3.75/0.97  --pred_elim                             true
% 3.75/0.97  --res_sim_input                         true
% 3.75/0.97  --eq_ax_congr_red                       true
% 3.75/0.97  --pure_diseq_elim                       true
% 3.75/0.97  --brand_transform                       false
% 3.75/0.97  --non_eq_to_eq                          false
% 3.75/0.97  --prep_def_merge                        true
% 3.75/0.97  --prep_def_merge_prop_impl              false
% 3.75/0.97  --prep_def_merge_mbd                    true
% 3.75/0.97  --prep_def_merge_tr_red                 false
% 3.75/0.97  --prep_def_merge_tr_cl                  false
% 3.75/0.97  --smt_preprocessing                     true
% 3.75/0.97  --smt_ac_axioms                         fast
% 3.75/0.97  --preprocessed_out                      false
% 3.75/0.97  --preprocessed_stats                    false
% 3.75/0.97  
% 3.75/0.97  ------ Abstraction refinement Options
% 3.75/0.97  
% 3.75/0.97  --abstr_ref                             []
% 3.75/0.97  --abstr_ref_prep                        false
% 3.75/0.97  --abstr_ref_until_sat                   false
% 3.75/0.97  --abstr_ref_sig_restrict                funpre
% 3.75/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/0.97  --abstr_ref_under                       []
% 3.75/0.97  
% 3.75/0.97  ------ SAT Options
% 3.75/0.97  
% 3.75/0.97  --sat_mode                              false
% 3.75/0.97  --sat_fm_restart_options                ""
% 3.75/0.97  --sat_gr_def                            false
% 3.75/0.97  --sat_epr_types                         true
% 3.75/0.97  --sat_non_cyclic_types                  false
% 3.75/0.97  --sat_finite_models                     false
% 3.75/0.97  --sat_fm_lemmas                         false
% 3.75/0.97  --sat_fm_prep                           false
% 3.75/0.97  --sat_fm_uc_incr                        true
% 3.75/0.97  --sat_out_model                         small
% 3.75/0.97  --sat_out_clauses                       false
% 3.75/0.97  
% 3.75/0.97  ------ QBF Options
% 3.75/0.97  
% 3.75/0.97  --qbf_mode                              false
% 3.75/0.97  --qbf_elim_univ                         false
% 3.75/0.97  --qbf_dom_inst                          none
% 3.75/0.97  --qbf_dom_pre_inst                      false
% 3.75/0.97  --qbf_sk_in                             false
% 3.75/0.97  --qbf_pred_elim                         true
% 3.75/0.97  --qbf_split                             512
% 3.75/0.97  
% 3.75/0.97  ------ BMC1 Options
% 3.75/0.97  
% 3.75/0.97  --bmc1_incremental                      false
% 3.75/0.97  --bmc1_axioms                           reachable_all
% 3.75/0.97  --bmc1_min_bound                        0
% 3.75/0.97  --bmc1_max_bound                        -1
% 3.75/0.97  --bmc1_max_bound_default                -1
% 3.75/0.97  --bmc1_symbol_reachability              true
% 3.75/0.97  --bmc1_property_lemmas                  false
% 3.75/0.97  --bmc1_k_induction                      false
% 3.75/0.97  --bmc1_non_equiv_states                 false
% 3.75/0.97  --bmc1_deadlock                         false
% 3.75/0.97  --bmc1_ucm                              false
% 3.75/0.97  --bmc1_add_unsat_core                   none
% 3.75/0.97  --bmc1_unsat_core_children              false
% 3.75/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/0.97  --bmc1_out_stat                         full
% 3.75/0.97  --bmc1_ground_init                      false
% 3.75/0.97  --bmc1_pre_inst_next_state              false
% 3.75/0.97  --bmc1_pre_inst_state                   false
% 3.75/0.97  --bmc1_pre_inst_reach_state             false
% 3.75/0.97  --bmc1_out_unsat_core                   false
% 3.75/0.97  --bmc1_aig_witness_out                  false
% 3.75/0.97  --bmc1_verbose                          false
% 3.75/0.97  --bmc1_dump_clauses_tptp                false
% 3.75/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.75/0.97  --bmc1_dump_file                        -
% 3.75/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.75/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.75/0.97  --bmc1_ucm_extend_mode                  1
% 3.75/0.97  --bmc1_ucm_init_mode                    2
% 3.75/0.97  --bmc1_ucm_cone_mode                    none
% 3.75/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.75/0.97  --bmc1_ucm_relax_model                  4
% 3.75/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.75/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/0.97  --bmc1_ucm_layered_model                none
% 3.75/0.97  --bmc1_ucm_max_lemma_size               10
% 3.75/0.97  
% 3.75/0.97  ------ AIG Options
% 3.75/0.97  
% 3.75/0.97  --aig_mode                              false
% 3.75/0.97  
% 3.75/0.97  ------ Instantiation Options
% 3.75/0.97  
% 3.75/0.97  --instantiation_flag                    true
% 3.75/0.97  --inst_sos_flag                         false
% 3.75/0.97  --inst_sos_phase                        true
% 3.75/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/0.97  --inst_lit_sel_side                     num_symb
% 3.75/0.97  --inst_solver_per_active                1400
% 3.75/0.97  --inst_solver_calls_frac                1.
% 3.75/0.97  --inst_passive_queue_type               priority_queues
% 3.75/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/0.97  --inst_passive_queues_freq              [25;2]
% 3.75/0.97  --inst_dismatching                      true
% 3.75/0.97  --inst_eager_unprocessed_to_passive     true
% 3.75/0.97  --inst_prop_sim_given                   true
% 3.75/0.97  --inst_prop_sim_new                     false
% 3.75/0.97  --inst_subs_new                         false
% 3.75/0.97  --inst_eq_res_simp                      false
% 3.75/0.97  --inst_subs_given                       false
% 3.75/0.97  --inst_orphan_elimination               true
% 3.75/0.97  --inst_learning_loop_flag               true
% 3.75/0.97  --inst_learning_start                   3000
% 3.75/0.97  --inst_learning_factor                  2
% 3.75/0.97  --inst_start_prop_sim_after_learn       3
% 3.75/0.97  --inst_sel_renew                        solver
% 3.75/0.97  --inst_lit_activity_flag                true
% 3.75/0.97  --inst_restr_to_given                   false
% 3.75/0.97  --inst_activity_threshold               500
% 3.75/0.97  --inst_out_proof                        true
% 3.75/0.97  
% 3.75/0.97  ------ Resolution Options
% 3.75/0.97  
% 3.75/0.97  --resolution_flag                       true
% 3.75/0.97  --res_lit_sel                           adaptive
% 3.75/0.97  --res_lit_sel_side                      none
% 3.75/0.97  --res_ordering                          kbo
% 3.75/0.97  --res_to_prop_solver                    active
% 3.75/0.97  --res_prop_simpl_new                    false
% 3.75/0.97  --res_prop_simpl_given                  true
% 3.75/0.97  --res_passive_queue_type                priority_queues
% 3.75/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/0.97  --res_passive_queues_freq               [15;5]
% 3.75/0.97  --res_forward_subs                      full
% 3.75/0.97  --res_backward_subs                     full
% 3.75/0.97  --res_forward_subs_resolution           true
% 3.75/0.97  --res_backward_subs_resolution          true
% 3.75/0.97  --res_orphan_elimination                true
% 3.75/0.97  --res_time_limit                        2.
% 3.75/0.97  --res_out_proof                         true
% 3.75/0.97  
% 3.75/0.97  ------ Superposition Options
% 3.75/0.97  
% 3.75/0.97  --superposition_flag                    true
% 3.75/0.97  --sup_passive_queue_type                priority_queues
% 3.75/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.75/0.97  --demod_completeness_check              fast
% 3.75/0.97  --demod_use_ground                      true
% 3.75/0.97  --sup_to_prop_solver                    passive
% 3.75/0.97  --sup_prop_simpl_new                    true
% 3.75/0.97  --sup_prop_simpl_given                  true
% 3.75/0.97  --sup_fun_splitting                     false
% 3.75/0.97  --sup_smt_interval                      50000
% 3.75/0.97  
% 3.75/0.97  ------ Superposition Simplification Setup
% 3.75/0.97  
% 3.75/0.97  --sup_indices_passive                   []
% 3.75/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.97  --sup_full_bw                           [BwDemod]
% 3.75/0.97  --sup_immed_triv                        [TrivRules]
% 3.75/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.97  --sup_immed_bw_main                     []
% 3.75/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/0.97  
% 3.75/0.97  ------ Combination Options
% 3.75/0.97  
% 3.75/0.97  --comb_res_mult                         3
% 3.75/0.97  --comb_sup_mult                         2
% 3.75/0.97  --comb_inst_mult                        10
% 3.75/0.97  
% 3.75/0.97  ------ Debug Options
% 3.75/0.97  
% 3.75/0.97  --dbg_backtrace                         false
% 3.75/0.97  --dbg_dump_prop_clauses                 false
% 3.75/0.97  --dbg_dump_prop_clauses_file            -
% 3.75/0.97  --dbg_out_stat                          false
% 3.75/0.97  ------ Parsing...
% 3.75/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.75/0.97  
% 3.75/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.75/0.97  
% 3.75/0.97  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.75/0.97  
% 3.75/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/0.97  ------ Proving...
% 3.75/0.97  ------ Problem Properties 
% 3.75/0.97  
% 3.75/0.97  
% 3.75/0.97  clauses                                 33
% 3.75/0.97  conjectures                             1
% 3.75/0.97  EPR                                     5
% 3.75/0.97  Horn                                    27
% 3.75/0.97  unary                                   3
% 3.75/0.97  binary                                  8
% 3.75/0.97  lits                                    96
% 3.75/0.97  lits eq                                 11
% 3.75/0.97  fd_pure                                 0
% 3.75/0.97  fd_pseudo                               0
% 3.75/0.97  fd_cond                                 0
% 3.75/0.97  fd_pseudo_cond                          2
% 3.75/0.97  AC symbols                              0
% 3.75/0.97  
% 3.75/0.97  ------ Schedule dynamic 5 is on 
% 3.75/0.97  
% 3.75/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.75/0.97  
% 3.75/0.97  
% 3.75/0.97  ------ 
% 3.75/0.97  Current options:
% 3.75/0.97  ------ 
% 3.75/0.97  
% 3.75/0.97  ------ Input Options
% 3.75/0.97  
% 3.75/0.97  --out_options                           all
% 3.75/0.97  --tptp_safe_out                         true
% 3.75/0.97  --problem_path                          ""
% 3.75/0.97  --include_path                          ""
% 3.75/0.97  --clausifier                            res/vclausify_rel
% 3.75/0.97  --clausifier_options                    --mode clausify
% 3.75/0.97  --stdin                                 false
% 3.75/0.97  --stats_out                             all
% 3.75/0.97  
% 3.75/0.97  ------ General Options
% 3.75/0.97  
% 3.75/0.97  --fof                                   false
% 3.75/0.97  --time_out_real                         305.
% 3.75/0.97  --time_out_virtual                      -1.
% 3.75/0.97  --symbol_type_check                     false
% 3.75/0.97  --clausify_out                          false
% 3.75/0.97  --sig_cnt_out                           false
% 3.75/0.97  --trig_cnt_out                          false
% 3.75/0.97  --trig_cnt_out_tolerance                1.
% 3.75/0.97  --trig_cnt_out_sk_spl                   false
% 3.75/0.97  --abstr_cl_out                          false
% 3.75/0.97  
% 3.75/0.97  ------ Global Options
% 3.75/0.97  
% 3.75/0.97  --schedule                              default
% 3.75/0.97  --add_important_lit                     false
% 3.75/0.97  --prop_solver_per_cl                    1000
% 3.75/0.97  --min_unsat_core                        false
% 3.75/0.97  --soft_assumptions                      false
% 3.75/0.97  --soft_lemma_size                       3
% 3.75/0.97  --prop_impl_unit_size                   0
% 3.75/0.97  --prop_impl_unit                        []
% 3.75/0.97  --share_sel_clauses                     true
% 3.75/0.97  --reset_solvers                         false
% 3.75/0.97  --bc_imp_inh                            [conj_cone]
% 3.75/0.97  --conj_cone_tolerance                   3.
% 3.75/0.97  --extra_neg_conj                        none
% 3.75/0.97  --large_theory_mode                     true
% 3.75/0.97  --prolific_symb_bound                   200
% 3.75/0.97  --lt_threshold                          2000
% 3.75/0.97  --clause_weak_htbl                      true
% 3.75/0.97  --gc_record_bc_elim                     false
% 3.75/0.97  
% 3.75/0.97  ------ Preprocessing Options
% 3.75/0.97  
% 3.75/0.97  --preprocessing_flag                    true
% 3.75/0.97  --time_out_prep_mult                    0.1
% 3.75/0.97  --splitting_mode                        input
% 3.75/0.97  --splitting_grd                         true
% 3.75/0.97  --splitting_cvd                         false
% 3.75/0.97  --splitting_cvd_svl                     false
% 3.75/0.97  --splitting_nvd                         32
% 3.75/0.97  --sub_typing                            true
% 3.75/0.97  --prep_gs_sim                           true
% 3.75/0.97  --prep_unflatten                        true
% 3.75/0.97  --prep_res_sim                          true
% 3.75/0.97  --prep_upred                            true
% 3.75/0.97  --prep_sem_filter                       exhaustive
% 3.75/0.97  --prep_sem_filter_out                   false
% 3.75/0.97  --pred_elim                             true
% 3.75/0.97  --res_sim_input                         true
% 3.75/0.97  --eq_ax_congr_red                       true
% 3.75/0.97  --pure_diseq_elim                       true
% 3.75/0.97  --brand_transform                       false
% 3.75/0.97  --non_eq_to_eq                          false
% 3.75/0.97  --prep_def_merge                        true
% 3.75/0.97  --prep_def_merge_prop_impl              false
% 3.75/0.97  --prep_def_merge_mbd                    true
% 3.75/0.97  --prep_def_merge_tr_red                 false
% 3.75/0.97  --prep_def_merge_tr_cl                  false
% 3.75/0.97  --smt_preprocessing                     true
% 3.75/0.97  --smt_ac_axioms                         fast
% 3.75/0.97  --preprocessed_out                      false
% 3.75/0.97  --preprocessed_stats                    false
% 3.75/0.97  
% 3.75/0.97  ------ Abstraction refinement Options
% 3.75/0.97  
% 3.75/0.97  --abstr_ref                             []
% 3.75/0.97  --abstr_ref_prep                        false
% 3.75/0.97  --abstr_ref_until_sat                   false
% 3.75/0.97  --abstr_ref_sig_restrict                funpre
% 3.75/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/0.97  --abstr_ref_under                       []
% 3.75/0.97  
% 3.75/0.97  ------ SAT Options
% 3.75/0.97  
% 3.75/0.97  --sat_mode                              false
% 3.75/0.97  --sat_fm_restart_options                ""
% 3.75/0.97  --sat_gr_def                            false
% 3.75/0.97  --sat_epr_types                         true
% 3.75/0.97  --sat_non_cyclic_types                  false
% 3.75/0.97  --sat_finite_models                     false
% 3.75/0.97  --sat_fm_lemmas                         false
% 3.75/0.97  --sat_fm_prep                           false
% 3.75/0.97  --sat_fm_uc_incr                        true
% 3.75/0.97  --sat_out_model                         small
% 3.75/0.97  --sat_out_clauses                       false
% 3.75/0.97  
% 3.75/0.97  ------ QBF Options
% 3.75/0.97  
% 3.75/0.97  --qbf_mode                              false
% 3.75/0.97  --qbf_elim_univ                         false
% 3.75/0.97  --qbf_dom_inst                          none
% 3.75/0.97  --qbf_dom_pre_inst                      false
% 3.75/0.97  --qbf_sk_in                             false
% 3.75/0.97  --qbf_pred_elim                         true
% 3.75/0.97  --qbf_split                             512
% 3.75/0.97  
% 3.75/0.97  ------ BMC1 Options
% 3.75/0.97  
% 3.75/0.97  --bmc1_incremental                      false
% 3.75/0.97  --bmc1_axioms                           reachable_all
% 3.75/0.97  --bmc1_min_bound                        0
% 3.75/0.97  --bmc1_max_bound                        -1
% 3.75/0.97  --bmc1_max_bound_default                -1
% 3.75/0.97  --bmc1_symbol_reachability              true
% 3.75/0.97  --bmc1_property_lemmas                  false
% 3.75/0.97  --bmc1_k_induction                      false
% 3.75/0.97  --bmc1_non_equiv_states                 false
% 3.75/0.97  --bmc1_deadlock                         false
% 3.75/0.97  --bmc1_ucm                              false
% 3.75/0.97  --bmc1_add_unsat_core                   none
% 3.75/0.97  --bmc1_unsat_core_children              false
% 3.75/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/0.97  --bmc1_out_stat                         full
% 3.75/0.97  --bmc1_ground_init                      false
% 3.75/0.97  --bmc1_pre_inst_next_state              false
% 3.75/0.97  --bmc1_pre_inst_state                   false
% 3.75/0.97  --bmc1_pre_inst_reach_state             false
% 3.75/0.97  --bmc1_out_unsat_core                   false
% 3.75/0.97  --bmc1_aig_witness_out                  false
% 3.75/0.97  --bmc1_verbose                          false
% 3.75/0.97  --bmc1_dump_clauses_tptp                false
% 3.75/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.75/0.97  --bmc1_dump_file                        -
% 3.75/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.75/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.75/0.97  --bmc1_ucm_extend_mode                  1
% 3.75/0.97  --bmc1_ucm_init_mode                    2
% 3.75/0.97  --bmc1_ucm_cone_mode                    none
% 3.75/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.75/0.97  --bmc1_ucm_relax_model                  4
% 3.75/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.75/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/0.97  --bmc1_ucm_layered_model                none
% 3.75/0.97  --bmc1_ucm_max_lemma_size               10
% 3.75/0.97  
% 3.75/0.97  ------ AIG Options
% 3.75/0.97  
% 3.75/0.97  --aig_mode                              false
% 3.75/0.97  
% 3.75/0.97  ------ Instantiation Options
% 3.75/0.97  
% 3.75/0.97  --instantiation_flag                    true
% 3.75/0.97  --inst_sos_flag                         false
% 3.75/0.97  --inst_sos_phase                        true
% 3.75/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/0.97  --inst_lit_sel_side                     none
% 3.75/0.97  --inst_solver_per_active                1400
% 3.75/0.97  --inst_solver_calls_frac                1.
% 3.75/0.97  --inst_passive_queue_type               priority_queues
% 3.75/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/0.97  --inst_passive_queues_freq              [25;2]
% 3.75/0.97  --inst_dismatching                      true
% 3.75/0.97  --inst_eager_unprocessed_to_passive     true
% 3.75/0.97  --inst_prop_sim_given                   true
% 3.75/0.97  --inst_prop_sim_new                     false
% 3.75/0.97  --inst_subs_new                         false
% 3.75/0.97  --inst_eq_res_simp                      false
% 3.75/0.97  --inst_subs_given                       false
% 3.75/0.97  --inst_orphan_elimination               true
% 3.75/0.97  --inst_learning_loop_flag               true
% 3.75/0.97  --inst_learning_start                   3000
% 3.75/0.97  --inst_learning_factor                  2
% 3.75/0.97  --inst_start_prop_sim_after_learn       3
% 3.75/0.97  --inst_sel_renew                        solver
% 3.75/0.97  --inst_lit_activity_flag                true
% 3.75/0.97  --inst_restr_to_given                   false
% 3.75/0.97  --inst_activity_threshold               500
% 3.75/0.97  --inst_out_proof                        true
% 3.75/0.97  
% 3.75/0.97  ------ Resolution Options
% 3.75/0.97  
% 3.75/0.97  --resolution_flag                       false
% 3.75/0.97  --res_lit_sel                           adaptive
% 3.75/0.97  --res_lit_sel_side                      none
% 3.75/0.97  --res_ordering                          kbo
% 3.75/0.97  --res_to_prop_solver                    active
% 3.75/0.97  --res_prop_simpl_new                    false
% 3.75/0.97  --res_prop_simpl_given                  true
% 3.75/0.97  --res_passive_queue_type                priority_queues
% 3.75/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/0.97  --res_passive_queues_freq               [15;5]
% 3.75/0.97  --res_forward_subs                      full
% 3.75/0.97  --res_backward_subs                     full
% 3.75/0.97  --res_forward_subs_resolution           true
% 3.75/0.97  --res_backward_subs_resolution          true
% 3.75/0.97  --res_orphan_elimination                true
% 3.75/0.97  --res_time_limit                        2.
% 3.75/0.97  --res_out_proof                         true
% 3.75/0.97  
% 3.75/0.97  ------ Superposition Options
% 3.75/0.97  
% 3.75/0.97  --superposition_flag                    true
% 3.75/0.97  --sup_passive_queue_type                priority_queues
% 3.75/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.75/0.97  --demod_completeness_check              fast
% 3.75/0.97  --demod_use_ground                      true
% 3.75/0.97  --sup_to_prop_solver                    passive
% 3.75/0.97  --sup_prop_simpl_new                    true
% 3.75/0.97  --sup_prop_simpl_given                  true
% 3.75/0.97  --sup_fun_splitting                     false
% 3.75/0.97  --sup_smt_interval                      50000
% 3.75/0.97  
% 3.75/0.97  ------ Superposition Simplification Setup
% 3.75/0.97  
% 3.75/0.97  --sup_indices_passive                   []
% 3.75/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.97  --sup_full_bw                           [BwDemod]
% 3.75/0.97  --sup_immed_triv                        [TrivRules]
% 3.75/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.97  --sup_immed_bw_main                     []
% 3.75/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/0.97  
% 3.75/0.97  ------ Combination Options
% 3.75/0.97  
% 3.75/0.97  --comb_res_mult                         3
% 3.75/0.97  --comb_sup_mult                         2
% 3.75/0.97  --comb_inst_mult                        10
% 3.75/0.97  
% 3.75/0.97  ------ Debug Options
% 3.75/0.97  
% 3.75/0.97  --dbg_backtrace                         false
% 3.75/0.97  --dbg_dump_prop_clauses                 false
% 3.75/0.97  --dbg_dump_prop_clauses_file            -
% 3.75/0.97  --dbg_out_stat                          false
% 3.75/0.97  
% 3.75/0.97  
% 3.75/0.97  
% 3.75/0.97  
% 3.75/0.97  ------ Proving...
% 3.75/0.97  
% 3.75/0.97  
% 3.75/0.97  % SZS status Theorem for theBenchmark.p
% 3.75/0.97  
% 3.75/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.75/0.97  
% 3.75/0.97  fof(f15,conjecture,(
% 3.75/0.97    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.75/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.97  
% 3.75/0.97  fof(f16,negated_conjecture,(
% 3.75/0.97    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.75/0.97    inference(negated_conjecture,[],[f15])).
% 3.75/0.97  
% 3.75/0.97  fof(f33,plain,(
% 3.75/0.97    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 3.75/0.97    inference(ennf_transformation,[],[f16])).
% 3.75/0.97  
% 3.75/0.97  fof(f50,plain,(
% 3.75/0.97    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7)) & r2_hidden(sK7,k1_funct_2(sK5,sK6)))),
% 3.75/0.97    introduced(choice_axiom,[])).
% 3.75/0.97  
% 3.75/0.97  fof(f51,plain,(
% 3.75/0.97    (~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7)) & r2_hidden(sK7,k1_funct_2(sK5,sK6))),
% 3.75/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f33,f50])).
% 3.75/0.97  
% 3.75/0.97  fof(f88,plain,(
% 3.75/0.97    r2_hidden(sK7,k1_funct_2(sK5,sK6))),
% 3.75/0.97    inference(cnf_transformation,[],[f51])).
% 3.75/0.97  
% 3.75/0.97  fof(f13,axiom,(
% 3.75/0.97    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 3.75/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.97  
% 3.75/0.97  fof(f34,plain,(
% 3.75/0.97    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 3.75/0.97    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.75/0.97  
% 3.75/0.97  fof(f35,plain,(
% 3.75/0.97    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 3.75/0.97    inference(definition_folding,[],[f13,f34])).
% 3.75/0.97  
% 3.75/0.97  fof(f49,plain,(
% 3.75/0.97    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 3.75/0.97    inference(nnf_transformation,[],[f35])).
% 3.75/0.97  
% 3.75/0.97  fof(f83,plain,(
% 3.75/0.97    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 3.75/0.97    inference(cnf_transformation,[],[f49])).
% 3.75/0.97  
% 3.75/0.97  fof(f95,plain,(
% 3.75/0.97    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 3.75/0.97    inference(equality_resolution,[],[f83])).
% 3.75/0.97  
% 3.75/0.97  fof(f43,plain,(
% 3.75/0.97    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 3.75/0.97    inference(nnf_transformation,[],[f34])).
% 3.75/0.97  
% 3.75/0.97  fof(f44,plain,(
% 3.75/0.97    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 3.75/0.97    inference(rectify,[],[f43])).
% 3.75/0.97  
% 3.75/0.97  fof(f47,plain,(
% 3.75/0.97    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0) & k1_relat_1(sK4(X0,X1,X6)) = X1 & sK4(X0,X1,X6) = X6 & v1_funct_1(sK4(X0,X1,X6)) & v1_relat_1(sK4(X0,X1,X6))))),
% 3.75/0.97    introduced(choice_axiom,[])).
% 3.75/0.97  
% 3.75/0.97  fof(f46,plain,(
% 3.75/0.97    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK3(X0,X1,X2)),X0) & k1_relat_1(sK3(X0,X1,X2)) = X1 & sK3(X0,X1,X2) = X3 & v1_funct_1(sK3(X0,X1,X2)) & v1_relat_1(sK3(X0,X1,X2))))) )),
% 3.75/0.97    introduced(choice_axiom,[])).
% 3.75/0.97  
% 3.75/0.97  fof(f45,plain,(
% 3.75/0.97    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK2(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK2(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.75/0.97    introduced(choice_axiom,[])).
% 3.75/0.97  
% 3.75/0.97  fof(f48,plain,(
% 3.75/0.97    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK2(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK3(X0,X1,X2)),X0) & k1_relat_1(sK3(X0,X1,X2)) = X1 & sK2(X0,X1,X2) = sK3(X0,X1,X2) & v1_funct_1(sK3(X0,X1,X2)) & v1_relat_1(sK3(X0,X1,X2))) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0) & k1_relat_1(sK4(X0,X1,X6)) = X1 & sK4(X0,X1,X6) = X6 & v1_funct_1(sK4(X0,X1,X6)) & v1_relat_1(sK4(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 3.75/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f44,f47,f46,f45])).
% 3.75/0.97  
% 3.75/0.97  fof(f73,plain,(
% 3.75/0.97    ( ! [X6,X2,X0,X1] : (sK4(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.75/0.97    inference(cnf_transformation,[],[f48])).
% 3.75/0.97  
% 3.75/0.97  fof(f75,plain,(
% 3.75/0.97    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.75/0.97    inference(cnf_transformation,[],[f48])).
% 3.75/0.97  
% 3.75/0.97  fof(f3,axiom,(
% 3.75/0.97    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.75/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.97  
% 3.75/0.97  fof(f18,plain,(
% 3.75/0.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.75/0.97    inference(ennf_transformation,[],[f3])).
% 3.75/0.97  
% 3.75/0.97  fof(f19,plain,(
% 3.75/0.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.75/0.97    inference(flattening,[],[f18])).
% 3.75/0.97  
% 3.75/0.97  fof(f58,plain,(
% 3.75/0.97    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.75/0.97    inference(cnf_transformation,[],[f19])).
% 3.75/0.97  
% 3.75/0.97  fof(f4,axiom,(
% 3.75/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.75/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.97  
% 3.75/0.97  fof(f42,plain,(
% 3.75/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.75/0.97    inference(nnf_transformation,[],[f4])).
% 3.75/0.97  
% 3.75/0.97  fof(f60,plain,(
% 3.75/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.75/0.97    inference(cnf_transformation,[],[f42])).
% 3.75/0.97  
% 3.75/0.97  fof(f9,axiom,(
% 3.75/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.75/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.97  
% 3.75/0.97  fof(f24,plain,(
% 3.75/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.75/0.97    inference(ennf_transformation,[],[f9])).
% 3.75/0.97  
% 3.75/0.97  fof(f25,plain,(
% 3.75/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.75/0.97    inference(flattening,[],[f24])).
% 3.75/0.97  
% 3.75/0.97  fof(f65,plain,(
% 3.75/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.75/0.97    inference(cnf_transformation,[],[f25])).
% 3.75/0.97  
% 3.75/0.97  fof(f74,plain,(
% 3.75/0.97    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK4(X0,X1,X6)) = X1 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.75/0.97    inference(cnf_transformation,[],[f48])).
% 3.75/0.97  
% 3.75/0.97  fof(f12,axiom,(
% 3.75/0.97    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.75/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.97  
% 3.75/0.97  fof(f29,plain,(
% 3.75/0.97    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.75/0.97    inference(ennf_transformation,[],[f12])).
% 3.75/0.97  
% 3.75/0.97  fof(f30,plain,(
% 3.75/0.97    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.75/0.97    inference(flattening,[],[f29])).
% 3.75/0.97  
% 3.75/0.97  fof(f70,plain,(
% 3.75/0.97    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.75/0.97    inference(cnf_transformation,[],[f30])).
% 3.75/0.97  
% 3.75/0.97  fof(f14,axiom,(
% 3.75/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.75/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.97  
% 3.75/0.97  fof(f31,plain,(
% 3.75/0.97    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.75/0.97    inference(ennf_transformation,[],[f14])).
% 3.75/0.97  
% 3.75/0.97  fof(f32,plain,(
% 3.75/0.97    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.75/0.97    inference(flattening,[],[f31])).
% 3.75/0.97  
% 3.75/0.97  fof(f86,plain,(
% 3.75/0.97    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.75/0.97    inference(cnf_transformation,[],[f32])).
% 3.75/0.97  
% 3.75/0.97  fof(f87,plain,(
% 3.75/0.97    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.75/0.97    inference(cnf_transformation,[],[f32])).
% 3.75/0.97  
% 3.75/0.97  fof(f10,axiom,(
% 3.75/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.75/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.97  
% 3.75/0.97  fof(f26,plain,(
% 3.75/0.97    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/0.97    inference(ennf_transformation,[],[f10])).
% 3.75/0.97  
% 3.75/0.97  fof(f27,plain,(
% 3.75/0.97    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/0.97    inference(flattening,[],[f26])).
% 3.75/0.97  
% 3.75/0.97  fof(f67,plain,(
% 3.75/0.97    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/0.97    inference(cnf_transformation,[],[f27])).
% 3.75/0.97  
% 3.75/0.97  fof(f89,plain,(
% 3.75/0.97    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7)),
% 3.75/0.97    inference(cnf_transformation,[],[f51])).
% 3.75/0.97  
% 3.75/0.97  fof(f2,axiom,(
% 3.75/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.75/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.97  
% 3.75/0.97  fof(f40,plain,(
% 3.75/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.75/0.97    inference(nnf_transformation,[],[f2])).
% 3.75/0.97  
% 3.75/0.97  fof(f41,plain,(
% 3.75/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.75/0.97    inference(flattening,[],[f40])).
% 3.75/0.97  
% 3.75/0.97  fof(f55,plain,(
% 3.75/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.75/0.97    inference(cnf_transformation,[],[f41])).
% 3.75/0.97  
% 3.75/0.97  fof(f91,plain,(
% 3.75/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.75/0.97    inference(equality_resolution,[],[f55])).
% 3.75/0.97  
% 3.75/0.97  fof(f57,plain,(
% 3.75/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.75/0.97    inference(cnf_transformation,[],[f41])).
% 3.75/0.97  
% 3.75/0.97  fof(f72,plain,(
% 3.75/0.97    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK4(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.75/0.97    inference(cnf_transformation,[],[f48])).
% 3.75/0.97  
% 3.75/0.97  fof(f71,plain,(
% 3.75/0.97    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK4(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.75/0.97    inference(cnf_transformation,[],[f48])).
% 3.75/0.97  
% 3.75/0.97  fof(f1,axiom,(
% 3.75/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.75/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.97  
% 3.75/0.97  fof(f17,plain,(
% 3.75/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.75/0.97    inference(ennf_transformation,[],[f1])).
% 3.75/0.97  
% 3.75/0.97  fof(f36,plain,(
% 3.75/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.75/0.97    inference(nnf_transformation,[],[f17])).
% 3.75/0.97  
% 3.75/0.97  fof(f37,plain,(
% 3.75/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.75/0.97    inference(rectify,[],[f36])).
% 3.75/0.97  
% 3.75/0.97  fof(f38,plain,(
% 3.75/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.75/0.97    introduced(choice_axiom,[])).
% 3.75/0.97  
% 3.75/0.97  fof(f39,plain,(
% 3.75/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.75/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 3.75/0.97  
% 3.75/0.97  fof(f53,plain,(
% 3.75/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.75/0.97    inference(cnf_transformation,[],[f39])).
% 3.75/0.97  
% 3.75/0.97  fof(f5,axiom,(
% 3.75/0.97    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.75/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.97  
% 3.75/0.97  fof(f20,plain,(
% 3.75/0.97    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.75/0.97    inference(ennf_transformation,[],[f5])).
% 3.75/0.97  
% 3.75/0.97  fof(f61,plain,(
% 3.75/0.97    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.75/0.97    inference(cnf_transformation,[],[f20])).
% 3.75/0.97  
% 3.75/0.97  fof(f8,axiom,(
% 3.75/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.75/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.97  
% 3.75/0.97  fof(f23,plain,(
% 3.75/0.97    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/0.97    inference(ennf_transformation,[],[f8])).
% 3.75/0.97  
% 3.75/0.97  fof(f64,plain,(
% 3.75/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/0.97    inference(cnf_transformation,[],[f23])).
% 3.75/0.97  
% 3.75/0.97  fof(f7,axiom,(
% 3.75/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.75/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.97  
% 3.75/0.97  fof(f22,plain,(
% 3.75/0.97    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/0.97    inference(ennf_transformation,[],[f7])).
% 3.75/0.97  
% 3.75/0.97  fof(f63,plain,(
% 3.75/0.97    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/0.97    inference(cnf_transformation,[],[f22])).
% 3.75/0.97  
% 3.75/0.97  fof(f59,plain,(
% 3.75/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.75/0.97    inference(cnf_transformation,[],[f42])).
% 3.75/0.97  
% 3.75/0.97  fof(f6,axiom,(
% 3.75/0.97    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.75/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.97  
% 3.75/0.97  fof(f21,plain,(
% 3.75/0.97    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.75/0.97    inference(ennf_transformation,[],[f6])).
% 3.75/0.97  
% 3.75/0.97  fof(f62,plain,(
% 3.75/0.97    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.75/0.97    inference(cnf_transformation,[],[f21])).
% 3.75/0.97  
% 3.75/0.97  fof(f11,axiom,(
% 3.75/0.97    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 3.75/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.97  
% 3.75/0.97  fof(f28,plain,(
% 3.75/0.97    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.75/0.97    inference(ennf_transformation,[],[f11])).
% 3.75/0.97  
% 3.75/0.97  fof(f68,plain,(
% 3.75/0.97    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.75/0.97    inference(cnf_transformation,[],[f28])).
% 3.75/0.97  
% 3.75/0.97  cnf(c_37,negated_conjecture,
% 3.75/0.97      ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) ),
% 3.75/0.97      inference(cnf_transformation,[],[f88]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5175,plain,
% 3.75/0.97      ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) = iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_32,plain,
% 3.75/0.97      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 3.75/0.97      inference(cnf_transformation,[],[f95]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5177,plain,
% 3.75/0.97      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_28,plain,
% 3.75/0.97      ( ~ sP0(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK4(X0,X1,X3) = X3 ),
% 3.75/0.97      inference(cnf_transformation,[],[f73]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5181,plain,
% 3.75/0.97      ( sK4(X0,X1,X2) = X2
% 3.75/0.97      | sP0(X0,X1,X3) != iProver_top
% 3.75/0.97      | r2_hidden(X2,X3) != iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_6961,plain,
% 3.75/0.97      ( sK4(X0,X1,X2) = X2
% 3.75/0.97      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5177,c_5181]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_7175,plain,
% 3.75/0.97      ( sK4(sK6,sK5,sK7) = sK7 ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5175,c_6961]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_26,plain,
% 3.75/0.97      ( ~ sP0(X0,X1,X2)
% 3.75/0.97      | ~ r2_hidden(X3,X2)
% 3.75/0.97      | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0) ),
% 3.75/0.97      inference(cnf_transformation,[],[f75]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5183,plain,
% 3.75/0.97      ( sP0(X0,X1,X2) != iProver_top
% 3.75/0.97      | r2_hidden(X3,X2) != iProver_top
% 3.75/0.97      | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0) = iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_7749,plain,
% 3.75/0.97      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 3.75/0.97      | r1_tarski(k2_relat_1(sK4(X2,X1,X0)),X2) = iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5177,c_5183]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_10602,plain,
% 3.75/0.97      ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) != iProver_top
% 3.75/0.97      | r1_tarski(k2_relat_1(sK7),sK6) = iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_7175,c_7749]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_38,plain,
% 3.75/0.97      ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) = iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_11074,plain,
% 3.75/0.97      ( r1_tarski(k2_relat_1(sK7),sK6) = iProver_top ),
% 3.75/0.97      inference(global_propositional_subsumption,
% 3.75/0.97                [status(thm)],
% 3.75/0.97                [c_10602,c_38]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_6,plain,
% 3.75/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.75/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5197,plain,
% 3.75/0.97      ( r1_tarski(X0,X1) != iProver_top
% 3.75/0.97      | r1_tarski(X1,X2) != iProver_top
% 3.75/0.97      | r1_tarski(X0,X2) = iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_11080,plain,
% 3.75/0.97      ( r1_tarski(k2_relat_1(sK7),X0) = iProver_top
% 3.75/0.97      | r1_tarski(sK6,X0) != iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_11074,c_5197]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_7,plain,
% 3.75/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.75/0.97      inference(cnf_transformation,[],[f60]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5196,plain,
% 3.75/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.75/0.97      | r1_tarski(X0,X1) != iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_13,plain,
% 3.75/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.97      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.75/0.97      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.75/0.97      | ~ v1_relat_1(X0) ),
% 3.75/0.97      inference(cnf_transformation,[],[f65]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5191,plain,
% 3.75/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.75/0.97      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.75/0.97      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.75/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_27,plain,
% 3.75/0.97      ( ~ sP0(X0,X1,X2)
% 3.75/0.97      | ~ r2_hidden(X3,X2)
% 3.75/0.97      | k1_relat_1(sK4(X0,X1,X3)) = X1 ),
% 3.75/0.97      inference(cnf_transformation,[],[f74]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5182,plain,
% 3.75/0.97      ( k1_relat_1(sK4(X0,X1,X2)) = X1
% 3.75/0.97      | sP0(X0,X1,X3) != iProver_top
% 3.75/0.97      | r2_hidden(X2,X3) != iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_7052,plain,
% 3.75/0.97      ( k1_relat_1(sK4(X0,X1,X2)) = X1
% 3.75/0.97      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5177,c_5182]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_7581,plain,
% 3.75/0.97      ( k1_relat_1(sK4(sK6,sK5,sK7)) = sK5 ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5175,c_7052]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_7583,plain,
% 3.75/0.97      ( k1_relat_1(sK7) = sK5 ),
% 3.75/0.97      inference(light_normalisation,[status(thm)],[c_7581,c_7175]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_17,plain,
% 3.75/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 3.75/0.97      | v1_partfun1(X0,X1)
% 3.75/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.97      | ~ v1_funct_1(X0)
% 3.75/0.97      | v1_xboole_0(X2) ),
% 3.75/0.97      inference(cnf_transformation,[],[f70]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_34,plain,
% 3.75/0.97      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.75/0.97      | ~ v1_funct_1(X0)
% 3.75/0.97      | ~ v1_relat_1(X0) ),
% 3.75/0.97      inference(cnf_transformation,[],[f86]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_522,plain,
% 3.75/0.97      ( v1_partfun1(X0,X1)
% 3.75/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.97      | ~ v1_funct_1(X3)
% 3.75/0.97      | ~ v1_funct_1(X0)
% 3.75/0.97      | ~ v1_relat_1(X3)
% 3.75/0.97      | v1_xboole_0(X2)
% 3.75/0.97      | X3 != X0
% 3.75/0.97      | k2_relat_1(X3) != X2
% 3.75/0.97      | k1_relat_1(X3) != X1 ),
% 3.75/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_34]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_523,plain,
% 3.75/0.97      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.75/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.75/0.97      | ~ v1_funct_1(X0)
% 3.75/0.97      | ~ v1_relat_1(X0)
% 3.75/0.97      | v1_xboole_0(k2_relat_1(X0)) ),
% 3.75/0.97      inference(unflattening,[status(thm)],[c_522]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_33,plain,
% 3.75/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.75/0.97      | ~ v1_funct_1(X0)
% 3.75/0.97      | ~ v1_relat_1(X0) ),
% 3.75/0.97      inference(cnf_transformation,[],[f87]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_527,plain,
% 3.75/0.97      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.75/0.97      | ~ v1_funct_1(X0)
% 3.75/0.97      | ~ v1_relat_1(X0)
% 3.75/0.97      | v1_xboole_0(k2_relat_1(X0)) ),
% 3.75/0.97      inference(global_propositional_subsumption,
% 3.75/0.97                [status(thm)],
% 3.75/0.97                [c_523,c_33]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_14,plain,
% 3.75/0.97      ( v1_funct_2(X0,X1,X2)
% 3.75/0.97      | ~ v1_partfun1(X0,X1)
% 3.75/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.97      | ~ v1_funct_1(X0) ),
% 3.75/0.97      inference(cnf_transformation,[],[f67]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_36,negated_conjecture,
% 3.75/0.97      ( ~ v1_funct_2(sK7,sK5,sK6)
% 3.75/0.97      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.75/0.97      | ~ v1_funct_1(sK7) ),
% 3.75/0.97      inference(cnf_transformation,[],[f89]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_546,plain,
% 3.75/0.97      ( ~ v1_partfun1(X0,X1)
% 3.75/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.97      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.75/0.97      | ~ v1_funct_1(X0)
% 3.75/0.97      | ~ v1_funct_1(sK7)
% 3.75/0.97      | sK6 != X2
% 3.75/0.97      | sK5 != X1
% 3.75/0.97      | sK7 != X0 ),
% 3.75/0.97      inference(resolution_lifted,[status(thm)],[c_14,c_36]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_547,plain,
% 3.75/0.97      ( ~ v1_partfun1(sK7,sK5)
% 3.75/0.97      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.75/0.97      | ~ v1_funct_1(sK7) ),
% 3.75/0.97      inference(unflattening,[status(thm)],[c_546]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_611,plain,
% 3.75/0.97      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.75/0.97      | ~ v1_funct_1(X0)
% 3.75/0.97      | ~ v1_funct_1(sK7)
% 3.75/0.97      | ~ v1_relat_1(X0)
% 3.75/0.97      | v1_xboole_0(k2_relat_1(X0))
% 3.75/0.97      | k1_relat_1(X0) != sK5
% 3.75/0.97      | sK7 != X0 ),
% 3.75/0.97      inference(resolution_lifted,[status(thm)],[c_527,c_547]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_612,plain,
% 3.75/0.97      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.75/0.97      | ~ v1_funct_1(sK7)
% 3.75/0.97      | ~ v1_relat_1(sK7)
% 3.75/0.97      | v1_xboole_0(k2_relat_1(sK7))
% 3.75/0.97      | k1_relat_1(sK7) != sK5 ),
% 3.75/0.97      inference(unflattening,[status(thm)],[c_611]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5170,plain,
% 3.75/0.97      ( k1_relat_1(sK7) != sK5
% 3.75/0.97      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.75/0.97      | v1_funct_1(sK7) != iProver_top
% 3.75/0.97      | v1_relat_1(sK7) != iProver_top
% 3.75/0.97      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_7593,plain,
% 3.75/0.97      ( sK5 != sK5
% 3.75/0.97      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.75/0.97      | v1_funct_1(sK7) != iProver_top
% 3.75/0.97      | v1_relat_1(sK7) != iProver_top
% 3.75/0.97      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.75/0.97      inference(demodulation,[status(thm)],[c_7583,c_5170]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_7604,plain,
% 3.75/0.97      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.75/0.97      | v1_funct_1(sK7) != iProver_top
% 3.75/0.97      | v1_relat_1(sK7) != iProver_top
% 3.75/0.97      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.75/0.97      inference(equality_resolution_simp,[status(thm)],[c_7593]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5,plain,
% 3.75/0.97      ( r1_tarski(X0,X0) ),
% 3.75/0.97      inference(cnf_transformation,[],[f91]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_121,plain,
% 3.75/0.97      ( r1_tarski(sK7,sK7) ),
% 3.75/0.97      inference(instantiation,[status(thm)],[c_5]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_3,plain,
% 3.75/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.75/0.97      inference(cnf_transformation,[],[f57]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_125,plain,
% 3.75/0.97      ( ~ r1_tarski(sK7,sK7) | sK7 = sK7 ),
% 3.75/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_613,plain,
% 3.75/0.97      ( k1_relat_1(sK7) != sK5
% 3.75/0.97      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.75/0.97      | v1_funct_1(sK7) != iProver_top
% 3.75/0.97      | v1_relat_1(sK7) != iProver_top
% 3.75/0.97      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_29,plain,
% 3.75/0.97      ( ~ sP0(X0,X1,X2)
% 3.75/0.97      | ~ r2_hidden(X3,X2)
% 3.75/0.97      | v1_funct_1(sK4(X0,X1,X3)) ),
% 3.75/0.97      inference(cnf_transformation,[],[f72]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5496,plain,
% 3.75/0.97      ( ~ sP0(X0,X1,k1_funct_2(sK5,sK6))
% 3.75/0.97      | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
% 3.75/0.97      | v1_funct_1(sK4(X0,X1,sK7)) ),
% 3.75/0.97      inference(instantiation,[status(thm)],[c_29]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5604,plain,
% 3.75/0.97      ( ~ sP0(sK6,sK5,k1_funct_2(sK5,sK6))
% 3.75/0.97      | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
% 3.75/0.97      | v1_funct_1(sK4(sK6,sK5,sK7)) ),
% 3.75/0.97      inference(instantiation,[status(thm)],[c_5496]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5606,plain,
% 3.75/0.97      ( sP0(sK6,sK5,k1_funct_2(sK5,sK6)) != iProver_top
% 3.75/0.97      | r2_hidden(sK7,k1_funct_2(sK5,sK6)) != iProver_top
% 3.75/0.97      | v1_funct_1(sK4(sK6,sK5,sK7)) = iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_5604]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5605,plain,
% 3.75/0.97      ( sP0(sK6,sK5,k1_funct_2(sK5,sK6)) ),
% 3.75/0.97      inference(instantiation,[status(thm)],[c_32]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5608,plain,
% 3.75/0.97      ( sP0(sK6,sK5,k1_funct_2(sK5,sK6)) = iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_5605]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_4401,plain,
% 3.75/0.97      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.75/0.97      theory(equality) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5723,plain,
% 3.75/0.97      ( v1_funct_1(X0)
% 3.75/0.97      | ~ v1_funct_1(sK4(sK6,sK5,sK7))
% 3.75/0.97      | X0 != sK4(sK6,sK5,sK7) ),
% 3.75/0.97      inference(instantiation,[status(thm)],[c_4401]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5724,plain,
% 3.75/0.97      ( X0 != sK4(sK6,sK5,sK7)
% 3.75/0.97      | v1_funct_1(X0) = iProver_top
% 3.75/0.97      | v1_funct_1(sK4(sK6,sK5,sK7)) != iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_5723]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5726,plain,
% 3.75/0.97      ( sK7 != sK4(sK6,sK5,sK7)
% 3.75/0.97      | v1_funct_1(sK4(sK6,sK5,sK7)) != iProver_top
% 3.75/0.97      | v1_funct_1(sK7) = iProver_top ),
% 3.75/0.97      inference(instantiation,[status(thm)],[c_5724]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_30,plain,
% 3.75/0.97      ( ~ sP0(X0,X1,X2)
% 3.75/0.97      | ~ r2_hidden(X3,X2)
% 3.75/0.97      | v1_relat_1(sK4(X0,X1,X3)) ),
% 3.75/0.97      inference(cnf_transformation,[],[f71]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5501,plain,
% 3.75/0.97      ( ~ sP0(X0,X1,k1_funct_2(sK5,sK6))
% 3.75/0.97      | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
% 3.75/0.97      | v1_relat_1(sK4(X0,X1,sK7)) ),
% 3.75/0.97      inference(instantiation,[status(thm)],[c_30]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5766,plain,
% 3.75/0.97      ( ~ sP0(sK6,sK5,k1_funct_2(sK5,sK6))
% 3.75/0.97      | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
% 3.75/0.97      | v1_relat_1(sK4(sK6,sK5,sK7)) ),
% 3.75/0.97      inference(instantiation,[status(thm)],[c_5501]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5768,plain,
% 3.75/0.97      ( sP0(sK6,sK5,k1_funct_2(sK5,sK6)) != iProver_top
% 3.75/0.97      | r2_hidden(sK7,k1_funct_2(sK5,sK6)) != iProver_top
% 3.75/0.97      | v1_relat_1(sK4(sK6,sK5,sK7)) = iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_5766]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5532,plain,
% 3.75/0.97      ( ~ sP0(X0,X1,k1_funct_2(sK5,sK6))
% 3.75/0.97      | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
% 3.75/0.97      | sK4(X0,X1,sK7) = sK7 ),
% 3.75/0.97      inference(instantiation,[status(thm)],[c_28]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5765,plain,
% 3.75/0.97      ( ~ sP0(sK6,sK5,k1_funct_2(sK5,sK6))
% 3.75/0.97      | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
% 3.75/0.97      | sK4(sK6,sK5,sK7) = sK7 ),
% 3.75/0.97      inference(instantiation,[status(thm)],[c_5532]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_4400,plain,
% 3.75/0.97      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 3.75/0.97      theory(equality) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5826,plain,
% 3.75/0.97      ( v1_relat_1(X0)
% 3.75/0.97      | ~ v1_relat_1(sK4(sK6,sK5,sK7))
% 3.75/0.97      | X0 != sK4(sK6,sK5,sK7) ),
% 3.75/0.97      inference(instantiation,[status(thm)],[c_4400]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5832,plain,
% 3.75/0.97      ( X0 != sK4(sK6,sK5,sK7)
% 3.75/0.97      | v1_relat_1(X0) = iProver_top
% 3.75/0.97      | v1_relat_1(sK4(sK6,sK5,sK7)) != iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_5826]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5834,plain,
% 3.75/0.97      ( sK7 != sK4(sK6,sK5,sK7)
% 3.75/0.97      | v1_relat_1(sK4(sK6,sK5,sK7)) != iProver_top
% 3.75/0.97      | v1_relat_1(sK7) = iProver_top ),
% 3.75/0.97      inference(instantiation,[status(thm)],[c_5832]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_4391,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5948,plain,
% 3.75/0.97      ( X0 != X1 | X0 = sK4(sK6,sK5,sK7) | sK4(sK6,sK5,sK7) != X1 ),
% 3.75/0.97      inference(instantiation,[status(thm)],[c_4391]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5949,plain,
% 3.75/0.97      ( sK4(sK6,sK5,sK7) != sK7 | sK7 = sK4(sK6,sK5,sK7) | sK7 != sK7 ),
% 3.75/0.97      inference(instantiation,[status(thm)],[c_5948]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_8978,plain,
% 3.75/0.97      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.75/0.97      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.75/0.97      inference(global_propositional_subsumption,
% 3.75/0.97                [status(thm)],
% 3.75/0.97                [c_7604,c_37,c_38,c_121,c_125,c_613,c_5606,c_5605,c_5608,
% 3.75/0.97                 c_5726,c_5768,c_5765,c_5834,c_5949,c_7583]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_9271,plain,
% 3.75/0.97      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 3.75/0.97      | r1_tarski(k1_relat_1(sK7),sK5) != iProver_top
% 3.75/0.97      | v1_relat_1(sK7) != iProver_top
% 3.75/0.97      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5191,c_8978]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_9298,plain,
% 3.75/0.97      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 3.75/0.97      | r1_tarski(sK5,sK5) != iProver_top
% 3.75/0.97      | v1_relat_1(sK7) != iProver_top
% 3.75/0.97      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.75/0.97      inference(light_normalisation,[status(thm)],[c_9271,c_7583]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_9463,plain,
% 3.75/0.97      ( r1_tarski(sK5,sK5) != iProver_top
% 3.75/0.97      | r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 3.75/0.97      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.75/0.97      inference(global_propositional_subsumption,
% 3.75/0.97                [status(thm)],
% 3.75/0.97                [c_9298,c_37,c_38,c_121,c_125,c_5605,c_5608,c_5768,
% 3.75/0.97                 c_5765,c_5834,c_5949]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_9464,plain,
% 3.75/0.97      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 3.75/0.97      | r1_tarski(sK5,sK5) != iProver_top
% 3.75/0.97      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.75/0.97      inference(renaming,[status(thm)],[c_9463]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5198,plain,
% 3.75/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_9470,plain,
% 3.75/0.97      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 3.75/0.97      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.75/0.97      inference(forward_subsumption_resolution,
% 3.75/0.97                [status(thm)],
% 3.75/0.97                [c_9464,c_5198]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_11085,plain,
% 3.75/0.97      ( v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_11074,c_9470]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_1,plain,
% 3.75/0.97      ( r2_hidden(sK1(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.75/0.97      inference(cnf_transformation,[],[f53]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5201,plain,
% 3.75/0.97      ( r2_hidden(sK1(X0,X1),X0) = iProver_top
% 3.75/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_9,plain,
% 3.75/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.75/0.97      | ~ r2_hidden(X2,X0)
% 3.75/0.97      | ~ v1_xboole_0(X1) ),
% 3.75/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_284,plain,
% 3.75/0.97      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.75/0.97      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_285,plain,
% 3.75/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.75/0.97      inference(renaming,[status(thm)],[c_284]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_348,plain,
% 3.75/0.97      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 3.75/0.97      inference(bin_hyper_res,[status(thm)],[c_9,c_285]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5174,plain,
% 3.75/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.75/0.97      | r1_tarski(X1,X2) != iProver_top
% 3.75/0.97      | v1_xboole_0(X2) != iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5572,plain,
% 3.75/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.75/0.97      | v1_xboole_0(X1) != iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5198,c_5174]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5910,plain,
% 3.75/0.97      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5201,c_5572]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_12,plain,
% 3.75/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.97      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.75/0.97      inference(cnf_transformation,[],[f64]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5192,plain,
% 3.75/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.75/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_6149,plain,
% 3.75/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.75/0.97      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5196,c_5192]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_6259,plain,
% 3.75/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.75/0.97      | v1_xboole_0(X2) != iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5910,c_6149]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_11229,plain,
% 3.75/0.97      ( k1_relset_1(X0,X1,k2_relat_1(sK7)) = k1_relat_1(k2_relat_1(sK7)) ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_11085,c_6259]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_11,plain,
% 3.75/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.97      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.75/0.97      inference(cnf_transformation,[],[f63]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5193,plain,
% 3.75/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.75/0.97      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_12866,plain,
% 3.75/0.97      ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.75/0.97      | m1_subset_1(k1_relat_1(k2_relat_1(sK7)),k1_zfmisc_1(X0)) = iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_11229,c_5193]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_16981,plain,
% 3.75/0.97      ( m1_subset_1(k1_relat_1(k2_relat_1(sK7)),k1_zfmisc_1(X0)) = iProver_top
% 3.75/0.97      | r1_tarski(k2_relat_1(sK7),k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5196,c_12866]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_17117,plain,
% 3.75/0.97      ( m1_subset_1(k1_relat_1(k2_relat_1(sK7)),k1_zfmisc_1(X0)) = iProver_top
% 3.75/0.97      | r1_tarski(sK6,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_11080,c_16981]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_17114,plain,
% 3.75/0.97      ( m1_subset_1(k1_relat_1(k2_relat_1(sK7)),k1_zfmisc_1(X0)) = iProver_top
% 3.75/0.97      | v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5910,c_16981]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_17653,plain,
% 3.75/0.97      ( m1_subset_1(k1_relat_1(k2_relat_1(sK7)),k1_zfmisc_1(X0)) = iProver_top ),
% 3.75/0.97      inference(global_propositional_subsumption,
% 3.75/0.97                [status(thm)],
% 3.75/0.97                [c_17117,c_38,c_9470,c_10602,c_17114]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_8,plain,
% 3.75/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.75/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5195,plain,
% 3.75/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.75/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_17660,plain,
% 3.75/0.97      ( r1_tarski(k1_relat_1(k2_relat_1(sK7)),X0) = iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_17653,c_5195]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5176,plain,
% 3.75/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.75/0.97      | v1_funct_1(X0) != iProver_top
% 3.75/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_7615,plain,
% 3.75/0.97      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(sK7)))) = iProver_top
% 3.75/0.97      | v1_funct_1(sK7) != iProver_top
% 3.75/0.97      | v1_relat_1(sK7) != iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_7583,c_5176]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_8229,plain,
% 3.75/0.97      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(sK7)))) = iProver_top ),
% 3.75/0.97      inference(global_propositional_subsumption,
% 3.75/0.97                [status(thm)],
% 3.75/0.97                [c_7615,c_37,c_38,c_121,c_125,c_5606,c_5605,c_5608,
% 3.75/0.97                 c_5726,c_5768,c_5765,c_5834,c_5949]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_10,plain,
% 3.75/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.97      | ~ v1_xboole_0(X2)
% 3.75/0.97      | v1_xboole_0(X0) ),
% 3.75/0.97      inference(cnf_transformation,[],[f62]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5194,plain,
% 3.75/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.75/0.97      | v1_xboole_0(X2) != iProver_top
% 3.75/0.97      | v1_xboole_0(X0) = iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_8235,plain,
% 3.75/0.97      ( v1_xboole_0(k2_relat_1(sK7)) != iProver_top
% 3.75/0.97      | v1_xboole_0(sK7) = iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_8229,c_5194]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_11231,plain,
% 3.75/0.97      ( v1_xboole_0(sK7) = iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_11085,c_8235]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5199,plain,
% 3.75/0.97      ( X0 = X1
% 3.75/0.97      | r1_tarski(X1,X0) != iProver_top
% 3.75/0.97      | r1_tarski(X0,X1) != iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_6191,plain,
% 3.75/0.97      ( X0 = X1
% 3.75/0.97      | r1_tarski(X0,X1) != iProver_top
% 3.75/0.97      | v1_xboole_0(X1) != iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5910,c_5199]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_6472,plain,
% 3.75/0.97      ( X0 = X1
% 3.75/0.97      | v1_xboole_0(X0) != iProver_top
% 3.75/0.97      | v1_xboole_0(X1) != iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5910,c_6191]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_11228,plain,
% 3.75/0.97      ( k2_relat_1(sK7) = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_11085,c_6472]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_12884,plain,
% 3.75/0.97      ( k2_relat_1(sK7) = sK7 ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_11231,c_11228]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_18867,plain,
% 3.75/0.97      ( r1_tarski(sK5,X0) = iProver_top ),
% 3.75/0.97      inference(light_normalisation,
% 3.75/0.97                [status(thm)],
% 3.75/0.97                [c_17660,c_7583,c_12884]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_6927,plain,
% 3.75/0.97      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.75/0.97      | v1_xboole_0(X2) != iProver_top
% 3.75/0.97      | v1_xboole_0(X0) = iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5196,c_5194]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_18877,plain,
% 3.75/0.97      ( v1_xboole_0(X0) != iProver_top | v1_xboole_0(sK5) = iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_18867,c_6927]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_18917,plain,
% 3.75/0.97      ( v1_xboole_0(sK5) = iProver_top
% 3.75/0.97      | v1_xboole_0(sK7) != iProver_top ),
% 3.75/0.97      inference(instantiation,[status(thm)],[c_18877]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_16,plain,
% 3.75/0.97      ( v1_partfun1(X0,X1)
% 3.75/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.97      | ~ v1_xboole_0(X1) ),
% 3.75/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_593,plain,
% 3.75/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.97      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.75/0.97      | ~ v1_funct_1(sK7)
% 3.75/0.97      | ~ v1_xboole_0(X1)
% 3.75/0.97      | sK5 != X1
% 3.75/0.97      | sK7 != X0 ),
% 3.75/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_547]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_594,plain,
% 3.75/0.97      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0)))
% 3.75/0.97      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.75/0.97      | ~ v1_funct_1(sK7)
% 3.75/0.97      | ~ v1_xboole_0(sK5) ),
% 3.75/0.97      inference(unflattening,[status(thm)],[c_593]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_4388,plain,
% 3.75/0.97      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.75/0.97      | ~ v1_funct_1(sK7)
% 3.75/0.97      | ~ v1_xboole_0(sK5)
% 3.75/0.97      | sP0_iProver_split ),
% 3.75/0.97      inference(splitting,
% 3.75/0.97                [splitting(split),new_symbols(definition,[])],
% 3.75/0.97                [c_594]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5171,plain,
% 3.75/0.97      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.75/0.97      | v1_funct_1(sK7) != iProver_top
% 3.75/0.97      | v1_xboole_0(sK5) != iProver_top
% 3.75/0.97      | sP0_iProver_split = iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_4388]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_4387,plain,
% 3.75/0.97      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0)))
% 3.75/0.97      | ~ sP0_iProver_split ),
% 3.75/0.97      inference(splitting,
% 3.75/0.97                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.75/0.97                [c_594]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5172,plain,
% 3.75/0.97      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) != iProver_top
% 3.75/0.97      | sP0_iProver_split != iProver_top ),
% 3.75/0.97      inference(predicate_to_equality,[status(thm)],[c_4387]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5329,plain,
% 3.75/0.97      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.75/0.97      | v1_funct_1(sK7) != iProver_top
% 3.75/0.97      | v1_xboole_0(sK5) != iProver_top ),
% 3.75/0.97      inference(forward_subsumption_resolution,
% 3.75/0.97                [status(thm)],
% 3.75/0.97                [c_5171,c_5172]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_9272,plain,
% 3.75/0.97      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 3.75/0.97      | r1_tarski(k1_relat_1(sK7),sK5) != iProver_top
% 3.75/0.97      | v1_funct_1(sK7) != iProver_top
% 3.75/0.97      | v1_relat_1(sK7) != iProver_top
% 3.75/0.97      | v1_xboole_0(sK5) != iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5191,c_5329]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_9288,plain,
% 3.75/0.97      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 3.75/0.97      | r1_tarski(sK5,sK5) != iProver_top
% 3.75/0.97      | v1_funct_1(sK7) != iProver_top
% 3.75/0.97      | v1_relat_1(sK7) != iProver_top
% 3.75/0.97      | v1_xboole_0(sK5) != iProver_top ),
% 3.75/0.97      inference(light_normalisation,[status(thm)],[c_9272,c_7583]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_5744,plain,
% 3.75/0.97      ( r1_tarski(sK7,k2_zfmisc_1(sK5,sK6)) != iProver_top
% 3.75/0.97      | v1_funct_1(sK7) != iProver_top
% 3.75/0.97      | v1_xboole_0(sK5) != iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5196,c_5329]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_6003,plain,
% 3.75/0.97      ( v1_funct_1(sK7) != iProver_top
% 3.75/0.97      | v1_xboole_0(sK5) != iProver_top
% 3.75/0.97      | v1_xboole_0(sK7) != iProver_top ),
% 3.75/0.97      inference(superposition,[status(thm)],[c_5910,c_5744]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(c_9475,plain,
% 3.75/0.97      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 3.75/0.97      | v1_xboole_0(sK5) != iProver_top ),
% 3.75/0.97      inference(global_propositional_subsumption,
% 3.75/0.97                [status(thm)],
% 3.75/0.97                [c_9288,c_37,c_38,c_121,c_125,c_5606,c_5605,c_5608,
% 3.75/0.97                 c_5726,c_5765,c_5949,c_6003,c_8235,c_9470]) ).
% 3.75/0.97  
% 3.75/0.97  cnf(contradiction,plain,
% 3.75/0.97      ( $false ),
% 3.75/0.97      inference(minisat,
% 3.75/0.97                [status(thm)],
% 3.75/0.97                [c_18917,c_10602,c_9475,c_9470,c_8235,c_38]) ).
% 3.75/0.97  
% 3.75/0.97  
% 3.75/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.75/0.97  
% 3.75/0.97  ------                               Statistics
% 3.75/0.97  
% 3.75/0.97  ------ General
% 3.75/0.97  
% 3.75/0.97  abstr_ref_over_cycles:                  0
% 3.75/0.97  abstr_ref_under_cycles:                 0
% 3.75/0.97  gc_basic_clause_elim:                   0
% 3.75/0.97  forced_gc_time:                         0
% 3.75/0.97  parsing_time:                           0.009
% 3.75/0.97  unif_index_cands_time:                  0.
% 3.75/0.97  unif_index_add_time:                    0.
% 3.75/0.97  orderings_time:                         0.
% 3.75/0.97  out_proof_time:                         0.013
% 3.75/0.97  total_time:                             0.412
% 3.75/0.97  num_of_symbols:                         54
% 3.75/0.97  num_of_terms:                           13773
% 3.75/0.97  
% 3.75/0.97  ------ Preprocessing
% 3.75/0.97  
% 3.75/0.97  num_of_splits:                          1
% 3.75/0.97  num_of_split_atoms:                     1
% 3.75/0.97  num_of_reused_defs:                     0
% 3.75/0.97  num_eq_ax_congr_red:                    48
% 3.75/0.97  num_of_sem_filtered_clauses:            1
% 3.75/0.97  num_of_subtypes:                        0
% 3.75/0.97  monotx_restored_types:                  0
% 3.75/0.97  sat_num_of_epr_types:                   0
% 3.75/0.97  sat_num_of_non_cyclic_types:            0
% 3.75/0.97  sat_guarded_non_collapsed_types:        0
% 3.75/0.97  num_pure_diseq_elim:                    0
% 3.75/0.97  simp_replaced_by:                       0
% 3.75/0.97  res_preprocessed:                       163
% 3.75/0.97  prep_upred:                             0
% 3.75/0.97  prep_unflattend:                        146
% 3.75/0.97  smt_new_axioms:                         0
% 3.75/0.97  pred_elim_cands:                        7
% 3.75/0.97  pred_elim:                              2
% 3.75/0.97  pred_elim_cl:                           2
% 3.75/0.97  pred_elim_cycles:                       9
% 3.75/0.97  merged_defs:                            8
% 3.75/0.97  merged_defs_ncl:                        0
% 3.75/0.97  bin_hyper_res:                          9
% 3.75/0.97  prep_cycles:                            4
% 3.75/0.97  pred_elim_time:                         0.06
% 3.75/0.97  splitting_time:                         0.
% 3.75/0.97  sem_filter_time:                        0.
% 3.75/0.97  monotx_time:                            0.001
% 3.75/0.97  subtype_inf_time:                       0.
% 3.75/0.97  
% 3.75/0.97  ------ Problem properties
% 3.75/0.97  
% 3.75/0.97  clauses:                                33
% 3.75/0.97  conjectures:                            1
% 3.75/0.97  epr:                                    5
% 3.75/0.97  horn:                                   27
% 3.75/0.97  ground:                                 4
% 3.75/0.97  unary:                                  3
% 3.75/0.97  binary:                                 8
% 3.75/0.97  lits:                                   96
% 3.75/0.97  lits_eq:                                11
% 3.75/0.97  fd_pure:                                0
% 3.75/0.97  fd_pseudo:                              0
% 3.75/0.97  fd_cond:                                0
% 3.75/0.97  fd_pseudo_cond:                         2
% 3.75/0.97  ac_symbols:                             0
% 3.75/0.97  
% 3.75/0.97  ------ Propositional Solver
% 3.75/0.97  
% 3.75/0.97  prop_solver_calls:                      28
% 3.75/0.97  prop_fast_solver_calls:                 2176
% 3.75/0.97  smt_solver_calls:                       0
% 3.75/0.97  smt_fast_solver_calls:                  0
% 3.75/0.97  prop_num_of_clauses:                    5608
% 3.75/0.97  prop_preprocess_simplified:             12993
% 3.75/0.97  prop_fo_subsumed:                       51
% 3.75/0.97  prop_solver_time:                       0.
% 3.75/0.97  smt_solver_time:                        0.
% 3.75/0.97  smt_fast_solver_time:                   0.
% 3.75/0.97  prop_fast_solver_time:                  0.
% 3.75/0.97  prop_unsat_core_time:                   0.
% 3.75/0.97  
% 3.75/0.97  ------ QBF
% 3.75/0.97  
% 3.75/0.97  qbf_q_res:                              0
% 3.75/0.97  qbf_num_tautologies:                    0
% 3.75/0.97  qbf_prep_cycles:                        0
% 3.75/0.97  
% 3.75/0.97  ------ BMC1
% 3.75/0.97  
% 3.75/0.97  bmc1_current_bound:                     -1
% 3.75/0.97  bmc1_last_solved_bound:                 -1
% 3.75/0.97  bmc1_unsat_core_size:                   -1
% 3.75/0.97  bmc1_unsat_core_parents_size:           -1
% 3.75/0.97  bmc1_merge_next_fun:                    0
% 3.75/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.75/0.97  
% 3.75/0.97  ------ Instantiation
% 3.75/0.97  
% 3.75/0.97  inst_num_of_clauses:                    1198
% 3.75/0.97  inst_num_in_passive:                    343
% 3.75/0.97  inst_num_in_active:                     512
% 3.75/0.97  inst_num_in_unprocessed:                343
% 3.75/0.97  inst_num_of_loops:                      750
% 3.75/0.97  inst_num_of_learning_restarts:          0
% 3.75/0.97  inst_num_moves_active_passive:          235
% 3.75/0.97  inst_lit_activity:                      0
% 3.75/0.97  inst_lit_activity_moves:                0
% 3.75/0.97  inst_num_tautologies:                   0
% 3.75/0.97  inst_num_prop_implied:                  0
% 3.75/0.97  inst_num_existing_simplified:           0
% 3.75/0.97  inst_num_eq_res_simplified:             0
% 3.75/0.97  inst_num_child_elim:                    0
% 3.75/0.97  inst_num_of_dismatching_blockings:      816
% 3.75/0.97  inst_num_of_non_proper_insts:           1568
% 3.75/0.97  inst_num_of_duplicates:                 0
% 3.75/0.97  inst_inst_num_from_inst_to_res:         0
% 3.75/0.97  inst_dismatching_checking_time:         0.
% 3.75/0.97  
% 3.75/0.97  ------ Resolution
% 3.75/0.97  
% 3.75/0.97  res_num_of_clauses:                     0
% 3.75/0.97  res_num_in_passive:                     0
% 3.75/0.97  res_num_in_active:                      0
% 3.75/0.97  res_num_of_loops:                       167
% 3.75/0.97  res_forward_subset_subsumed:            116
% 3.75/0.97  res_backward_subset_subsumed:           0
% 3.75/0.97  res_forward_subsumed:                   0
% 3.75/0.97  res_backward_subsumed:                  0
% 3.75/0.97  res_forward_subsumption_resolution:     2
% 3.75/0.97  res_backward_subsumption_resolution:    0
% 3.75/0.97  res_clause_to_clause_subsumption:       1540
% 3.75/0.97  res_orphan_elimination:                 0
% 3.75/0.97  res_tautology_del:                      160
% 3.75/0.97  res_num_eq_res_simplified:              0
% 3.75/0.97  res_num_sel_changes:                    0
% 3.75/0.97  res_moves_from_active_to_pass:          0
% 3.75/0.97  
% 3.75/0.97  ------ Superposition
% 3.75/0.97  
% 3.75/0.97  sup_time_total:                         0.
% 3.75/0.97  sup_time_generating:                    0.
% 3.75/0.97  sup_time_sim_full:                      0.
% 3.75/0.97  sup_time_sim_immed:                     0.
% 3.75/0.97  
% 3.75/0.97  sup_num_of_clauses:                     339
% 3.75/0.97  sup_num_in_active:                      84
% 3.75/0.97  sup_num_in_passive:                     255
% 3.75/0.97  sup_num_of_loops:                       148
% 3.75/0.97  sup_fw_superposition:                   173
% 3.75/0.97  sup_bw_superposition:                   293
% 3.75/0.97  sup_immediate_simplified:               87
% 3.75/0.97  sup_given_eliminated:                   1
% 3.75/0.97  comparisons_done:                       0
% 3.75/0.97  comparisons_avoided:                    0
% 3.75/0.97  
% 3.75/0.97  ------ Simplifications
% 3.75/0.97  
% 3.75/0.97  
% 3.75/0.97  sim_fw_subset_subsumed:                 31
% 3.75/0.97  sim_bw_subset_subsumed:                 17
% 3.75/0.97  sim_fw_subsumed:                        37
% 3.75/0.97  sim_bw_subsumed:                        0
% 3.75/0.97  sim_fw_subsumption_res:                 2
% 3.75/0.97  sim_bw_subsumption_res:                 0
% 3.75/0.97  sim_tautology_del:                      7
% 3.75/0.97  sim_eq_tautology_del:                   14
% 3.75/0.97  sim_eq_res_simp:                        2
% 3.75/0.97  sim_fw_demodulated:                     1
% 3.75/0.97  sim_bw_demodulated:                     61
% 3.75/0.97  sim_light_normalised:                   25
% 3.75/0.97  sim_joinable_taut:                      0
% 3.75/0.97  sim_joinable_simp:                      0
% 3.75/0.97  sim_ac_normalised:                      0
% 3.75/0.97  sim_smt_subsumption:                    0
% 3.75/0.97  
%------------------------------------------------------------------------------

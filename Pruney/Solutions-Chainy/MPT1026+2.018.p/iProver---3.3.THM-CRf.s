%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:15 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  170 (4891 expanded)
%              Number of clauses        :  109 (1595 expanded)
%              Number of leaves         :   17 (1259 expanded)
%              Depth                    :   32
%              Number of atoms          :  583 (30602 expanded)
%              Number of equality atoms :  304 (10168 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
        | ~ v1_funct_2(sK6,sK4,sK5)
        | ~ v1_funct_1(sK6) )
      & r2_hidden(sK6,k1_funct_2(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      | ~ v1_funct_2(sK6,sK4,sK5)
      | ~ v1_funct_1(sK6) )
    & r2_hidden(sK6,k1_funct_2(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f36])).

fof(f70,plain,(
    r2_hidden(sK6,k1_funct_2(sK4,sK5)) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f21,plain,(
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

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f9,f21])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f68])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X0)
          & k1_relat_1(X8) = X1
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK3(X0,X1,X6)),X0)
        & k1_relat_1(sK3(X0,X1,X6)) = X1
        & sK3(X0,X1,X6) = X6
        & v1_funct_1(sK3(X0,X1,X6))
        & v1_relat_1(sK3(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X0)
          & k1_relat_1(X5) = X1
          & X3 = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK2(X0,X1,X2)),X0)
        & k1_relat_1(sK2(X0,X1,X2)) = X1
        & sK2(X0,X1,X2) = X3
        & v1_funct_1(sK2(X0,X1,X2))
        & v1_relat_1(sK2(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
              | sK1(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X0)
              & k1_relat_1(X5) = X1
              & sK1(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | k1_relat_1(X4) != X1
                | sK1(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK2(X0,X1,X2)),X0)
              & k1_relat_1(sK2(X0,X1,X2)) = X1
              & sK1(X0,X1,X2) = sK2(X0,X1,X2)
              & v1_funct_1(sK2(X0,X1,X2))
              & v1_relat_1(sK2(X0,X1,X2)) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | k1_relat_1(X7) != X1
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK3(X0,X1,X6)),X0)
                & k1_relat_1(sK3(X0,X1,X6)) = X1
                & sK3(X0,X1,X6) = X6
                & v1_funct_1(sK3(X0,X1,X6))
                & v1_relat_1(sK3(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f33,f32,f31])).

fof(f58,plain,(
    ! [X6,X2,X0,X1] :
      ( sK3(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK3(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK3(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK3(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_2(sK6,sK4,sK5)
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK3(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f53])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f43])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_6568,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_6571,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_33,negated_conjecture,
    ( r2_hidden(sK6,k1_funct_2(sK4,sK5)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_6553,plain,
    ( r2_hidden(sK6,k1_funct_2(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_31,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6554,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_27,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK3(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_6558,plain,
    ( sK3(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7407,plain,
    ( sK3(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6554,c_6558])).

cnf(c_7412,plain,
    ( sK3(sK5,sK4,sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_6553,c_7407])).

cnf(c_25,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | r1_tarski(k2_relat_1(sK3(X0,X1,X3)),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_6560,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK3(X0,X1,X3)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8120,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(sK3(X2,X1,X0)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6554,c_6560])).

cnf(c_8772,plain,
    ( r2_hidden(sK6,k1_funct_2(sK4,sK5)) != iProver_top
    | r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_7412,c_8120])).

cnf(c_34,plain,
    ( r2_hidden(sK6,k1_funct_2(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8800,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8772,c_34])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_6569,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9072,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6568,c_6569])).

cnf(c_10773,plain,
    ( k1_relset_1(X0,sK5,sK6) = k1_relat_1(sK6)
    | r1_tarski(k1_relat_1(sK6),X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8800,c_9072])).

cnf(c_26,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK3(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_6559,plain,
    ( k1_relat_1(sK3(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7768,plain,
    ( k1_relat_1(sK3(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6554,c_6559])).

cnf(c_8044,plain,
    ( k1_relat_1(sK3(sK5,sK4,sK6)) = sK4 ),
    inference(superposition,[status(thm)],[c_6553,c_7768])).

cnf(c_8045,plain,
    ( k1_relat_1(sK6) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_8044,c_7412])).

cnf(c_10777,plain,
    ( k1_relset_1(X0,sK5,sK6) = sK4
    | r1_tarski(sK4,X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10773,c_8045])).

cnf(c_29,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK3(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_6556,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | v1_relat_1(sK3(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7656,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | v1_relat_1(sK3(X2,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6554,c_6556])).

cnf(c_7871,plain,
    ( v1_relat_1(sK3(sK5,sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6553,c_7656])).

cnf(c_7872,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7871,c_7412])).

cnf(c_11004,plain,
    ( r1_tarski(sK4,X0) != iProver_top
    | k1_relset_1(X0,sK5,sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10777,c_7872])).

cnf(c_11005,plain,
    ( k1_relset_1(X0,sK5,sK6) = sK4
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11004])).

cnf(c_11012,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4 ),
    inference(superposition,[status(thm)],[c_6571,c_11005])).

cnf(c_15,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(sK6,sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1072,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK6)
    | k1_relset_1(X1,X2,X0) != X1
    | sK5 != X2
    | sK4 != X1
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_1073,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK6)
    | k1_relset_1(sK4,sK5,sK6) != sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_1072])).

cnf(c_6549,plain,
    ( k1_relset_1(sK4,sK5,sK6) != sK4
    | k1_xboole_0 = sK5
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1073])).

cnf(c_11221,plain,
    ( sK5 = k1_xboole_0
    | sK4 != sK4
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11012,c_6549])).

cnf(c_11223,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11221])).

cnf(c_28,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK3(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_6557,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | v1_funct_1(sK3(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7662,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | v1_funct_1(sK3(X2,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6554,c_6557])).

cnf(c_7975,plain,
    ( v1_funct_1(sK3(sK5,sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6553,c_7662])).

cnf(c_7976,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7975,c_7412])).

cnf(c_6101,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_10415,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_6101])).

cnf(c_11225,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11223,c_7976,c_10415,c_11221])).

cnf(c_11226,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11225])).

cnf(c_11231,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
    | r1_tarski(k1_relat_1(sK6),sK4) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6568,c_11226])).

cnf(c_11232,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
    | r1_tarski(sK4,sK4) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11231,c_8045])).

cnf(c_8956,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_8959,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8956])).

cnf(c_11391,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11232,c_34,c_7872,c_8772,c_8959])).

cnf(c_11402,plain,
    ( r2_hidden(sK6,k1_funct_2(sK4,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11391,c_6553])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_6570,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_6572,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7339,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6570,c_6572])).

cnf(c_8775,plain,
    ( k2_relat_1(sK3(k1_xboole_0,X0,X1)) = k1_xboole_0
    | r2_hidden(X1,k1_funct_2(X0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8120,c_7339])).

cnf(c_11460,plain,
    ( k2_relat_1(sK3(k1_xboole_0,sK4,sK6)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11402,c_8775])).

cnf(c_11399,plain,
    ( sK3(k1_xboole_0,sK4,sK6) = sK6 ),
    inference(demodulation,[status(thm)],[c_11391,c_7412])).

cnf(c_12485,plain,
    ( k2_relat_1(sK6) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11460,c_11399])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_9070,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_6568])).

cnf(c_9239,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6571,c_9070])).

cnf(c_12525,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_12485,c_9239])).

cnf(c_113,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_115,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_113])).

cnf(c_13380,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12525,c_115,c_7872])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_9,c_8])).

cnf(c_6552,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_7505,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_6552])).

cnf(c_13385,plain,
    ( r1_tarski(k1_relat_1(sK6),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_13380,c_7505])).

cnf(c_13396,plain,
    ( r1_tarski(sK4,X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13385,c_8045])).

cnf(c_13487,plain,
    ( r1_tarski(sK4,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13396,c_7872])).

cnf(c_13495,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13487,c_7339])).

cnf(c_7018,plain,
    ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_6569])).

cnf(c_13387,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_13380,c_7018])).

cnf(c_13389,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK6) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_13387,c_8045])).

cnf(c_14,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1053,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK6)
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK5 != X1
    | sK4 != k1_xboole_0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_32])).

cnf(c_1054,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
    | ~ v1_funct_1(sK6)
    | k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1053])).

cnf(c_6550,plain,
    ( k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1054])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_6697,plain,
    ( k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6550,c_5])).

cnf(c_11401,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) != k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11391,c_6697])).

cnf(c_11410,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) != k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11401,c_4])).

cnf(c_114,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_7977,plain,
    ( v1_funct_1(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7976])).

cnf(c_6103,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_8961,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,X1)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_6103])).

cnf(c_8963,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8961])).

cnf(c_9071,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_6568])).

cnf(c_9272,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8800,c_9071])).

cnf(c_9568,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9272,c_8045])).

cnf(c_9612,plain,
    ( r1_tarski(sK4,k1_xboole_0) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9568,c_7872])).

cnf(c_9613,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9612])).

cnf(c_9614,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(sK4,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9613])).

cnf(c_11452,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(sK6)
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11410])).

cnf(c_11890,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11410,c_114,c_7977,c_8963,c_9614,c_11452])).

cnf(c_13404,plain,
    ( sK4 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13389,c_11890])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13495,c_13404])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:02:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.50/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/0.98  
% 3.50/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.50/0.98  
% 3.50/0.98  ------  iProver source info
% 3.50/0.98  
% 3.50/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.50/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.50/0.98  git: non_committed_changes: false
% 3.50/0.98  git: last_make_outside_of_git: false
% 3.50/0.98  
% 3.50/0.98  ------ 
% 3.50/0.98  
% 3.50/0.98  ------ Input Options
% 3.50/0.98  
% 3.50/0.98  --out_options                           all
% 3.50/0.98  --tptp_safe_out                         true
% 3.50/0.98  --problem_path                          ""
% 3.50/0.98  --include_path                          ""
% 3.50/0.98  --clausifier                            res/vclausify_rel
% 3.50/0.98  --clausifier_options                    --mode clausify
% 3.50/0.98  --stdin                                 false
% 3.50/0.98  --stats_out                             all
% 3.50/0.98  
% 3.50/0.98  ------ General Options
% 3.50/0.98  
% 3.50/0.98  --fof                                   false
% 3.50/0.98  --time_out_real                         305.
% 3.50/0.98  --time_out_virtual                      -1.
% 3.50/0.98  --symbol_type_check                     false
% 3.50/0.98  --clausify_out                          false
% 3.50/0.98  --sig_cnt_out                           false
% 3.50/0.99  --trig_cnt_out                          false
% 3.50/0.99  --trig_cnt_out_tolerance                1.
% 3.50/0.99  --trig_cnt_out_sk_spl                   false
% 3.50/0.99  --abstr_cl_out                          false
% 3.50/0.99  
% 3.50/0.99  ------ Global Options
% 3.50/0.99  
% 3.50/0.99  --schedule                              default
% 3.50/0.99  --add_important_lit                     false
% 3.50/0.99  --prop_solver_per_cl                    1000
% 3.50/0.99  --min_unsat_core                        false
% 3.50/0.99  --soft_assumptions                      false
% 3.50/0.99  --soft_lemma_size                       3
% 3.50/0.99  --prop_impl_unit_size                   0
% 3.50/0.99  --prop_impl_unit                        []
% 3.50/0.99  --share_sel_clauses                     true
% 3.50/0.99  --reset_solvers                         false
% 3.50/0.99  --bc_imp_inh                            [conj_cone]
% 3.50/0.99  --conj_cone_tolerance                   3.
% 3.50/0.99  --extra_neg_conj                        none
% 3.50/0.99  --large_theory_mode                     true
% 3.50/0.99  --prolific_symb_bound                   200
% 3.50/0.99  --lt_threshold                          2000
% 3.50/0.99  --clause_weak_htbl                      true
% 3.50/0.99  --gc_record_bc_elim                     false
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing Options
% 3.50/0.99  
% 3.50/0.99  --preprocessing_flag                    true
% 3.50/0.99  --time_out_prep_mult                    0.1
% 3.50/0.99  --splitting_mode                        input
% 3.50/0.99  --splitting_grd                         true
% 3.50/0.99  --splitting_cvd                         false
% 3.50/0.99  --splitting_cvd_svl                     false
% 3.50/0.99  --splitting_nvd                         32
% 3.50/0.99  --sub_typing                            true
% 3.50/0.99  --prep_gs_sim                           true
% 3.50/0.99  --prep_unflatten                        true
% 3.50/0.99  --prep_res_sim                          true
% 3.50/0.99  --prep_upred                            true
% 3.50/0.99  --prep_sem_filter                       exhaustive
% 3.50/0.99  --prep_sem_filter_out                   false
% 3.50/0.99  --pred_elim                             true
% 3.50/0.99  --res_sim_input                         true
% 3.50/0.99  --eq_ax_congr_red                       true
% 3.50/0.99  --pure_diseq_elim                       true
% 3.50/0.99  --brand_transform                       false
% 3.50/0.99  --non_eq_to_eq                          false
% 3.50/0.99  --prep_def_merge                        true
% 3.50/0.99  --prep_def_merge_prop_impl              false
% 3.50/0.99  --prep_def_merge_mbd                    true
% 3.50/0.99  --prep_def_merge_tr_red                 false
% 3.50/0.99  --prep_def_merge_tr_cl                  false
% 3.50/0.99  --smt_preprocessing                     true
% 3.50/0.99  --smt_ac_axioms                         fast
% 3.50/0.99  --preprocessed_out                      false
% 3.50/0.99  --preprocessed_stats                    false
% 3.50/0.99  
% 3.50/0.99  ------ Abstraction refinement Options
% 3.50/0.99  
% 3.50/0.99  --abstr_ref                             []
% 3.50/0.99  --abstr_ref_prep                        false
% 3.50/0.99  --abstr_ref_until_sat                   false
% 3.50/0.99  --abstr_ref_sig_restrict                funpre
% 3.50/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/0.99  --abstr_ref_under                       []
% 3.50/0.99  
% 3.50/0.99  ------ SAT Options
% 3.50/0.99  
% 3.50/0.99  --sat_mode                              false
% 3.50/0.99  --sat_fm_restart_options                ""
% 3.50/0.99  --sat_gr_def                            false
% 3.50/0.99  --sat_epr_types                         true
% 3.50/0.99  --sat_non_cyclic_types                  false
% 3.50/0.99  --sat_finite_models                     false
% 3.50/0.99  --sat_fm_lemmas                         false
% 3.50/0.99  --sat_fm_prep                           false
% 3.50/0.99  --sat_fm_uc_incr                        true
% 3.50/0.99  --sat_out_model                         small
% 3.50/0.99  --sat_out_clauses                       false
% 3.50/0.99  
% 3.50/0.99  ------ QBF Options
% 3.50/0.99  
% 3.50/0.99  --qbf_mode                              false
% 3.50/0.99  --qbf_elim_univ                         false
% 3.50/0.99  --qbf_dom_inst                          none
% 3.50/0.99  --qbf_dom_pre_inst                      false
% 3.50/0.99  --qbf_sk_in                             false
% 3.50/0.99  --qbf_pred_elim                         true
% 3.50/0.99  --qbf_split                             512
% 3.50/0.99  
% 3.50/0.99  ------ BMC1 Options
% 3.50/0.99  
% 3.50/0.99  --bmc1_incremental                      false
% 3.50/0.99  --bmc1_axioms                           reachable_all
% 3.50/0.99  --bmc1_min_bound                        0
% 3.50/0.99  --bmc1_max_bound                        -1
% 3.50/0.99  --bmc1_max_bound_default                -1
% 3.50/0.99  --bmc1_symbol_reachability              true
% 3.50/0.99  --bmc1_property_lemmas                  false
% 3.50/0.99  --bmc1_k_induction                      false
% 3.50/0.99  --bmc1_non_equiv_states                 false
% 3.50/0.99  --bmc1_deadlock                         false
% 3.50/0.99  --bmc1_ucm                              false
% 3.50/0.99  --bmc1_add_unsat_core                   none
% 3.50/0.99  --bmc1_unsat_core_children              false
% 3.50/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/0.99  --bmc1_out_stat                         full
% 3.50/0.99  --bmc1_ground_init                      false
% 3.50/0.99  --bmc1_pre_inst_next_state              false
% 3.50/0.99  --bmc1_pre_inst_state                   false
% 3.50/0.99  --bmc1_pre_inst_reach_state             false
% 3.50/0.99  --bmc1_out_unsat_core                   false
% 3.50/0.99  --bmc1_aig_witness_out                  false
% 3.50/0.99  --bmc1_verbose                          false
% 3.50/0.99  --bmc1_dump_clauses_tptp                false
% 3.50/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.50/0.99  --bmc1_dump_file                        -
% 3.50/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.50/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.50/0.99  --bmc1_ucm_extend_mode                  1
% 3.50/0.99  --bmc1_ucm_init_mode                    2
% 3.50/0.99  --bmc1_ucm_cone_mode                    none
% 3.50/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.50/0.99  --bmc1_ucm_relax_model                  4
% 3.50/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.50/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/0.99  --bmc1_ucm_layered_model                none
% 3.50/0.99  --bmc1_ucm_max_lemma_size               10
% 3.50/0.99  
% 3.50/0.99  ------ AIG Options
% 3.50/0.99  
% 3.50/0.99  --aig_mode                              false
% 3.50/0.99  
% 3.50/0.99  ------ Instantiation Options
% 3.50/0.99  
% 3.50/0.99  --instantiation_flag                    true
% 3.50/0.99  --inst_sos_flag                         false
% 3.50/0.99  --inst_sos_phase                        true
% 3.50/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel_side                     num_symb
% 3.50/0.99  --inst_solver_per_active                1400
% 3.50/0.99  --inst_solver_calls_frac                1.
% 3.50/0.99  --inst_passive_queue_type               priority_queues
% 3.50/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/0.99  --inst_passive_queues_freq              [25;2]
% 3.50/0.99  --inst_dismatching                      true
% 3.50/0.99  --inst_eager_unprocessed_to_passive     true
% 3.50/0.99  --inst_prop_sim_given                   true
% 3.50/0.99  --inst_prop_sim_new                     false
% 3.50/0.99  --inst_subs_new                         false
% 3.50/0.99  --inst_eq_res_simp                      false
% 3.50/0.99  --inst_subs_given                       false
% 3.50/0.99  --inst_orphan_elimination               true
% 3.50/0.99  --inst_learning_loop_flag               true
% 3.50/0.99  --inst_learning_start                   3000
% 3.50/0.99  --inst_learning_factor                  2
% 3.50/0.99  --inst_start_prop_sim_after_learn       3
% 3.50/0.99  --inst_sel_renew                        solver
% 3.50/0.99  --inst_lit_activity_flag                true
% 3.50/0.99  --inst_restr_to_given                   false
% 3.50/0.99  --inst_activity_threshold               500
% 3.50/0.99  --inst_out_proof                        true
% 3.50/0.99  
% 3.50/0.99  ------ Resolution Options
% 3.50/0.99  
% 3.50/0.99  --resolution_flag                       true
% 3.50/0.99  --res_lit_sel                           adaptive
% 3.50/0.99  --res_lit_sel_side                      none
% 3.50/0.99  --res_ordering                          kbo
% 3.50/0.99  --res_to_prop_solver                    active
% 3.50/0.99  --res_prop_simpl_new                    false
% 3.50/0.99  --res_prop_simpl_given                  true
% 3.50/0.99  --res_passive_queue_type                priority_queues
% 3.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/0.99  --res_passive_queues_freq               [15;5]
% 3.50/0.99  --res_forward_subs                      full
% 3.50/0.99  --res_backward_subs                     full
% 3.50/0.99  --res_forward_subs_resolution           true
% 3.50/0.99  --res_backward_subs_resolution          true
% 3.50/0.99  --res_orphan_elimination                true
% 3.50/0.99  --res_time_limit                        2.
% 3.50/0.99  --res_out_proof                         true
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Options
% 3.50/0.99  
% 3.50/0.99  --superposition_flag                    true
% 3.50/0.99  --sup_passive_queue_type                priority_queues
% 3.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.50/0.99  --demod_completeness_check              fast
% 3.50/0.99  --demod_use_ground                      true
% 3.50/0.99  --sup_to_prop_solver                    passive
% 3.50/0.99  --sup_prop_simpl_new                    true
% 3.50/0.99  --sup_prop_simpl_given                  true
% 3.50/0.99  --sup_fun_splitting                     false
% 3.50/0.99  --sup_smt_interval                      50000
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Simplification Setup
% 3.50/0.99  
% 3.50/0.99  --sup_indices_passive                   []
% 3.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_full_bw                           [BwDemod]
% 3.50/0.99  --sup_immed_triv                        [TrivRules]
% 3.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_immed_bw_main                     []
% 3.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  
% 3.50/0.99  ------ Combination Options
% 3.50/0.99  
% 3.50/0.99  --comb_res_mult                         3
% 3.50/0.99  --comb_sup_mult                         2
% 3.50/0.99  --comb_inst_mult                        10
% 3.50/0.99  
% 3.50/0.99  ------ Debug Options
% 3.50/0.99  
% 3.50/0.99  --dbg_backtrace                         false
% 3.50/0.99  --dbg_dump_prop_clauses                 false
% 3.50/0.99  --dbg_dump_prop_clauses_file            -
% 3.50/0.99  --dbg_out_stat                          false
% 3.50/0.99  ------ Parsing...
% 3.50/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/0.99  ------ Proving...
% 3.50/0.99  ------ Problem Properties 
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  clauses                                 27
% 3.50/0.99  conjectures                             1
% 3.50/0.99  EPR                                     3
% 3.50/0.99  Horn                                    21
% 3.50/0.99  unary                                   6
% 3.50/0.99  binary                                  2
% 3.50/0.99  lits                                    79
% 3.50/0.99  lits eq                                 20
% 3.50/0.99  fd_pure                                 0
% 3.50/0.99  fd_pseudo                               0
% 3.50/0.99  fd_cond                                 1
% 3.50/0.99  fd_pseudo_cond                          2
% 3.50/0.99  AC symbols                              0
% 3.50/0.99  
% 3.50/0.99  ------ Schedule dynamic 5 is on 
% 3.50/0.99  
% 3.50/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  ------ 
% 3.50/0.99  Current options:
% 3.50/0.99  ------ 
% 3.50/0.99  
% 3.50/0.99  ------ Input Options
% 3.50/0.99  
% 3.50/0.99  --out_options                           all
% 3.50/0.99  --tptp_safe_out                         true
% 3.50/0.99  --problem_path                          ""
% 3.50/0.99  --include_path                          ""
% 3.50/0.99  --clausifier                            res/vclausify_rel
% 3.50/0.99  --clausifier_options                    --mode clausify
% 3.50/0.99  --stdin                                 false
% 3.50/0.99  --stats_out                             all
% 3.50/0.99  
% 3.50/0.99  ------ General Options
% 3.50/0.99  
% 3.50/0.99  --fof                                   false
% 3.50/0.99  --time_out_real                         305.
% 3.50/0.99  --time_out_virtual                      -1.
% 3.50/0.99  --symbol_type_check                     false
% 3.50/0.99  --clausify_out                          false
% 3.50/0.99  --sig_cnt_out                           false
% 3.50/0.99  --trig_cnt_out                          false
% 3.50/0.99  --trig_cnt_out_tolerance                1.
% 3.50/0.99  --trig_cnt_out_sk_spl                   false
% 3.50/0.99  --abstr_cl_out                          false
% 3.50/0.99  
% 3.50/0.99  ------ Global Options
% 3.50/0.99  
% 3.50/0.99  --schedule                              default
% 3.50/0.99  --add_important_lit                     false
% 3.50/0.99  --prop_solver_per_cl                    1000
% 3.50/0.99  --min_unsat_core                        false
% 3.50/0.99  --soft_assumptions                      false
% 3.50/0.99  --soft_lemma_size                       3
% 3.50/0.99  --prop_impl_unit_size                   0
% 3.50/0.99  --prop_impl_unit                        []
% 3.50/0.99  --share_sel_clauses                     true
% 3.50/0.99  --reset_solvers                         false
% 3.50/0.99  --bc_imp_inh                            [conj_cone]
% 3.50/0.99  --conj_cone_tolerance                   3.
% 3.50/0.99  --extra_neg_conj                        none
% 3.50/0.99  --large_theory_mode                     true
% 3.50/0.99  --prolific_symb_bound                   200
% 3.50/0.99  --lt_threshold                          2000
% 3.50/0.99  --clause_weak_htbl                      true
% 3.50/0.99  --gc_record_bc_elim                     false
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing Options
% 3.50/0.99  
% 3.50/0.99  --preprocessing_flag                    true
% 3.50/0.99  --time_out_prep_mult                    0.1
% 3.50/0.99  --splitting_mode                        input
% 3.50/0.99  --splitting_grd                         true
% 3.50/0.99  --splitting_cvd                         false
% 3.50/0.99  --splitting_cvd_svl                     false
% 3.50/0.99  --splitting_nvd                         32
% 3.50/0.99  --sub_typing                            true
% 3.50/0.99  --prep_gs_sim                           true
% 3.50/0.99  --prep_unflatten                        true
% 3.50/0.99  --prep_res_sim                          true
% 3.50/0.99  --prep_upred                            true
% 3.50/0.99  --prep_sem_filter                       exhaustive
% 3.50/0.99  --prep_sem_filter_out                   false
% 3.50/0.99  --pred_elim                             true
% 3.50/0.99  --res_sim_input                         true
% 3.50/0.99  --eq_ax_congr_red                       true
% 3.50/0.99  --pure_diseq_elim                       true
% 3.50/0.99  --brand_transform                       false
% 3.50/0.99  --non_eq_to_eq                          false
% 3.50/0.99  --prep_def_merge                        true
% 3.50/0.99  --prep_def_merge_prop_impl              false
% 3.50/0.99  --prep_def_merge_mbd                    true
% 3.50/0.99  --prep_def_merge_tr_red                 false
% 3.50/0.99  --prep_def_merge_tr_cl                  false
% 3.50/0.99  --smt_preprocessing                     true
% 3.50/0.99  --smt_ac_axioms                         fast
% 3.50/0.99  --preprocessed_out                      false
% 3.50/0.99  --preprocessed_stats                    false
% 3.50/0.99  
% 3.50/0.99  ------ Abstraction refinement Options
% 3.50/0.99  
% 3.50/0.99  --abstr_ref                             []
% 3.50/0.99  --abstr_ref_prep                        false
% 3.50/0.99  --abstr_ref_until_sat                   false
% 3.50/0.99  --abstr_ref_sig_restrict                funpre
% 3.50/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/0.99  --abstr_ref_under                       []
% 3.50/0.99  
% 3.50/0.99  ------ SAT Options
% 3.50/0.99  
% 3.50/0.99  --sat_mode                              false
% 3.50/0.99  --sat_fm_restart_options                ""
% 3.50/0.99  --sat_gr_def                            false
% 3.50/0.99  --sat_epr_types                         true
% 3.50/0.99  --sat_non_cyclic_types                  false
% 3.50/0.99  --sat_finite_models                     false
% 3.50/0.99  --sat_fm_lemmas                         false
% 3.50/0.99  --sat_fm_prep                           false
% 3.50/0.99  --sat_fm_uc_incr                        true
% 3.50/0.99  --sat_out_model                         small
% 3.50/0.99  --sat_out_clauses                       false
% 3.50/0.99  
% 3.50/0.99  ------ QBF Options
% 3.50/0.99  
% 3.50/0.99  --qbf_mode                              false
% 3.50/0.99  --qbf_elim_univ                         false
% 3.50/0.99  --qbf_dom_inst                          none
% 3.50/0.99  --qbf_dom_pre_inst                      false
% 3.50/0.99  --qbf_sk_in                             false
% 3.50/0.99  --qbf_pred_elim                         true
% 3.50/0.99  --qbf_split                             512
% 3.50/0.99  
% 3.50/0.99  ------ BMC1 Options
% 3.50/0.99  
% 3.50/0.99  --bmc1_incremental                      false
% 3.50/0.99  --bmc1_axioms                           reachable_all
% 3.50/0.99  --bmc1_min_bound                        0
% 3.50/0.99  --bmc1_max_bound                        -1
% 3.50/0.99  --bmc1_max_bound_default                -1
% 3.50/0.99  --bmc1_symbol_reachability              true
% 3.50/0.99  --bmc1_property_lemmas                  false
% 3.50/0.99  --bmc1_k_induction                      false
% 3.50/0.99  --bmc1_non_equiv_states                 false
% 3.50/0.99  --bmc1_deadlock                         false
% 3.50/0.99  --bmc1_ucm                              false
% 3.50/0.99  --bmc1_add_unsat_core                   none
% 3.50/0.99  --bmc1_unsat_core_children              false
% 3.50/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/0.99  --bmc1_out_stat                         full
% 3.50/0.99  --bmc1_ground_init                      false
% 3.50/0.99  --bmc1_pre_inst_next_state              false
% 3.50/0.99  --bmc1_pre_inst_state                   false
% 3.50/0.99  --bmc1_pre_inst_reach_state             false
% 3.50/0.99  --bmc1_out_unsat_core                   false
% 3.50/0.99  --bmc1_aig_witness_out                  false
% 3.50/0.99  --bmc1_verbose                          false
% 3.50/0.99  --bmc1_dump_clauses_tptp                false
% 3.50/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.50/0.99  --bmc1_dump_file                        -
% 3.50/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.50/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.50/0.99  --bmc1_ucm_extend_mode                  1
% 3.50/0.99  --bmc1_ucm_init_mode                    2
% 3.50/0.99  --bmc1_ucm_cone_mode                    none
% 3.50/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.50/0.99  --bmc1_ucm_relax_model                  4
% 3.50/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.50/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/0.99  --bmc1_ucm_layered_model                none
% 3.50/0.99  --bmc1_ucm_max_lemma_size               10
% 3.50/0.99  
% 3.50/0.99  ------ AIG Options
% 3.50/0.99  
% 3.50/0.99  --aig_mode                              false
% 3.50/0.99  
% 3.50/0.99  ------ Instantiation Options
% 3.50/0.99  
% 3.50/0.99  --instantiation_flag                    true
% 3.50/0.99  --inst_sos_flag                         false
% 3.50/0.99  --inst_sos_phase                        true
% 3.50/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel_side                     none
% 3.50/0.99  --inst_solver_per_active                1400
% 3.50/0.99  --inst_solver_calls_frac                1.
% 3.50/0.99  --inst_passive_queue_type               priority_queues
% 3.50/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/0.99  --inst_passive_queues_freq              [25;2]
% 3.50/0.99  --inst_dismatching                      true
% 3.50/0.99  --inst_eager_unprocessed_to_passive     true
% 3.50/0.99  --inst_prop_sim_given                   true
% 3.50/0.99  --inst_prop_sim_new                     false
% 3.50/0.99  --inst_subs_new                         false
% 3.50/0.99  --inst_eq_res_simp                      false
% 3.50/0.99  --inst_subs_given                       false
% 3.50/0.99  --inst_orphan_elimination               true
% 3.50/0.99  --inst_learning_loop_flag               true
% 3.50/0.99  --inst_learning_start                   3000
% 3.50/0.99  --inst_learning_factor                  2
% 3.50/0.99  --inst_start_prop_sim_after_learn       3
% 3.50/0.99  --inst_sel_renew                        solver
% 3.50/0.99  --inst_lit_activity_flag                true
% 3.50/0.99  --inst_restr_to_given                   false
% 3.50/0.99  --inst_activity_threshold               500
% 3.50/0.99  --inst_out_proof                        true
% 3.50/0.99  
% 3.50/0.99  ------ Resolution Options
% 3.50/0.99  
% 3.50/0.99  --resolution_flag                       false
% 3.50/0.99  --res_lit_sel                           adaptive
% 3.50/0.99  --res_lit_sel_side                      none
% 3.50/0.99  --res_ordering                          kbo
% 3.50/0.99  --res_to_prop_solver                    active
% 3.50/0.99  --res_prop_simpl_new                    false
% 3.50/0.99  --res_prop_simpl_given                  true
% 3.50/0.99  --res_passive_queue_type                priority_queues
% 3.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/0.99  --res_passive_queues_freq               [15;5]
% 3.50/0.99  --res_forward_subs                      full
% 3.50/0.99  --res_backward_subs                     full
% 3.50/0.99  --res_forward_subs_resolution           true
% 3.50/0.99  --res_backward_subs_resolution          true
% 3.50/0.99  --res_orphan_elimination                true
% 3.50/0.99  --res_time_limit                        2.
% 3.50/0.99  --res_out_proof                         true
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Options
% 3.50/0.99  
% 3.50/0.99  --superposition_flag                    true
% 3.50/0.99  --sup_passive_queue_type                priority_queues
% 3.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.50/0.99  --demod_completeness_check              fast
% 3.50/0.99  --demod_use_ground                      true
% 3.50/0.99  --sup_to_prop_solver                    passive
% 3.50/0.99  --sup_prop_simpl_new                    true
% 3.50/0.99  --sup_prop_simpl_given                  true
% 3.50/0.99  --sup_fun_splitting                     false
% 3.50/0.99  --sup_smt_interval                      50000
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Simplification Setup
% 3.50/0.99  
% 3.50/0.99  --sup_indices_passive                   []
% 3.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_full_bw                           [BwDemod]
% 3.50/0.99  --sup_immed_triv                        [TrivRules]
% 3.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_immed_bw_main                     []
% 3.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  
% 3.50/0.99  ------ Combination Options
% 3.50/0.99  
% 3.50/0.99  --comb_res_mult                         3
% 3.50/0.99  --comb_sup_mult                         2
% 3.50/0.99  --comb_inst_mult                        10
% 3.50/0.99  
% 3.50/0.99  ------ Debug Options
% 3.50/0.99  
% 3.50/0.99  --dbg_backtrace                         false
% 3.50/0.99  --dbg_dump_prop_clauses                 false
% 3.50/0.99  --dbg_dump_prop_clauses_file            -
% 3.50/0.99  --dbg_out_stat                          false
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  ------ Proving...
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  % SZS status Theorem for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  fof(f7,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f16,plain,(
% 3.50/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.50/0.99    inference(ennf_transformation,[],[f7])).
% 3.50/0.99  
% 3.50/0.99  fof(f17,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.50/0.99    inference(flattening,[],[f16])).
% 3.50/0.99  
% 3.50/0.99  fof(f49,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f17])).
% 3.50/0.99  
% 3.50/0.99  fof(f1,axiom,(
% 3.50/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f23,plain,(
% 3.50/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.50/0.99    inference(nnf_transformation,[],[f1])).
% 3.50/0.99  
% 3.50/0.99  fof(f24,plain,(
% 3.50/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.50/0.99    inference(flattening,[],[f23])).
% 3.50/0.99  
% 3.50/0.99  fof(f39,plain,(
% 3.50/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.50/0.99    inference(cnf_transformation,[],[f24])).
% 3.50/0.99  
% 3.50/0.99  fof(f72,plain,(
% 3.50/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.50/0.99    inference(equality_resolution,[],[f39])).
% 3.50/0.99  
% 3.50/0.99  fof(f10,conjecture,(
% 3.50/0.99    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f11,negated_conjecture,(
% 3.50/0.99    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.50/0.99    inference(negated_conjecture,[],[f10])).
% 3.50/0.99  
% 3.50/0.99  fof(f20,plain,(
% 3.50/0.99    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 3.50/0.99    inference(ennf_transformation,[],[f11])).
% 3.50/0.99  
% 3.50/0.99  fof(f36,plain,(
% 3.50/0.99    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6)) & r2_hidden(sK6,k1_funct_2(sK4,sK5)))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f37,plain,(
% 3.50/0.99    (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6)) & r2_hidden(sK6,k1_funct_2(sK4,sK5))),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f36])).
% 3.50/0.99  
% 3.50/0.99  fof(f70,plain,(
% 3.50/0.99    r2_hidden(sK6,k1_funct_2(sK4,sK5))),
% 3.50/0.99    inference(cnf_transformation,[],[f37])).
% 3.50/0.99  
% 3.50/0.99  fof(f9,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f21,plain,(
% 3.50/0.99    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 3.50/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.50/0.99  
% 3.50/0.99  fof(f22,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 3.50/0.99    inference(definition_folding,[],[f9,f21])).
% 3.50/0.99  
% 3.50/0.99  fof(f35,plain,(
% 3.50/0.99    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 3.50/0.99    inference(nnf_transformation,[],[f22])).
% 3.50/0.99  
% 3.50/0.99  fof(f68,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 3.50/0.99    inference(cnf_transformation,[],[f35])).
% 3.50/0.99  
% 3.50/0.99  fof(f84,plain,(
% 3.50/0.99    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 3.50/0.99    inference(equality_resolution,[],[f68])).
% 3.50/0.99  
% 3.50/0.99  fof(f29,plain,(
% 3.50/0.99    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 3.50/0.99    inference(nnf_transformation,[],[f21])).
% 3.50/0.99  
% 3.50/0.99  fof(f30,plain,(
% 3.50/0.99    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 3.50/0.99    inference(rectify,[],[f29])).
% 3.50/0.99  
% 3.50/0.99  fof(f33,plain,(
% 3.50/0.99    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK3(X0,X1,X6)),X0) & k1_relat_1(sK3(X0,X1,X6)) = X1 & sK3(X0,X1,X6) = X6 & v1_funct_1(sK3(X0,X1,X6)) & v1_relat_1(sK3(X0,X1,X6))))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f32,plain,(
% 3.50/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK2(X0,X1,X2)),X0) & k1_relat_1(sK2(X0,X1,X2)) = X1 & sK2(X0,X1,X2) = X3 & v1_funct_1(sK2(X0,X1,X2)) & v1_relat_1(sK2(X0,X1,X2))))) )),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f31,plain,(
% 3.50/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK1(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK1(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f34,plain,(
% 3.50/0.99    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK1(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK2(X0,X1,X2)),X0) & k1_relat_1(sK2(X0,X1,X2)) = X1 & sK1(X0,X1,X2) = sK2(X0,X1,X2) & v1_funct_1(sK2(X0,X1,X2)) & v1_relat_1(sK2(X0,X1,X2))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK3(X0,X1,X6)),X0) & k1_relat_1(sK3(X0,X1,X6)) = X1 & sK3(X0,X1,X6) = X6 & v1_funct_1(sK3(X0,X1,X6)) & v1_relat_1(sK3(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f33,f32,f31])).
% 3.50/0.99  
% 3.50/0.99  fof(f58,plain,(
% 3.50/0.99    ( ! [X6,X2,X0,X1] : (sK3(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f34])).
% 3.50/0.99  
% 3.50/0.99  fof(f60,plain,(
% 3.50/0.99    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK3(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f34])).
% 3.50/0.99  
% 3.50/0.99  fof(f6,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f15,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/0.99    inference(ennf_transformation,[],[f6])).
% 3.50/0.99  
% 3.50/0.99  fof(f48,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f15])).
% 3.50/0.99  
% 3.50/0.99  fof(f59,plain,(
% 3.50/0.99    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK3(X0,X1,X6)) = X1 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f34])).
% 3.50/0.99  
% 3.50/0.99  fof(f56,plain,(
% 3.50/0.99    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK3(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f34])).
% 3.50/0.99  
% 3.50/0.99  fof(f8,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f18,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/0.99    inference(ennf_transformation,[],[f8])).
% 3.50/0.99  
% 3.50/0.99  fof(f19,plain,(
% 3.50/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/0.99    inference(flattening,[],[f18])).
% 3.50/0.99  
% 3.50/0.99  fof(f28,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/0.99    inference(nnf_transformation,[],[f19])).
% 3.50/0.99  
% 3.50/0.99  fof(f52,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f28])).
% 3.50/0.99  
% 3.50/0.99  fof(f71,plain,(
% 3.50/0.99    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_2(sK6,sK4,sK5) | ~v1_funct_1(sK6)),
% 3.50/0.99    inference(cnf_transformation,[],[f37])).
% 3.50/0.99  
% 3.50/0.99  fof(f57,plain,(
% 3.50/0.99    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK3(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f34])).
% 3.50/0.99  
% 3.50/0.99  fof(f2,axiom,(
% 3.50/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f41,plain,(
% 3.50/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f2])).
% 3.50/0.99  
% 3.50/0.99  fof(f40,plain,(
% 3.50/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f24])).
% 3.50/0.99  
% 3.50/0.99  fof(f3,axiom,(
% 3.50/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f25,plain,(
% 3.50/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.50/0.99    inference(nnf_transformation,[],[f3])).
% 3.50/0.99  
% 3.50/0.99  fof(f26,plain,(
% 3.50/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.50/0.99    inference(flattening,[],[f25])).
% 3.50/0.99  
% 3.50/0.99  fof(f44,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.50/0.99    inference(cnf_transformation,[],[f26])).
% 3.50/0.99  
% 3.50/0.99  fof(f74,plain,(
% 3.50/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.50/0.99    inference(equality_resolution,[],[f44])).
% 3.50/0.99  
% 3.50/0.99  fof(f5,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f12,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.50/0.99    inference(pure_predicate_removal,[],[f5])).
% 3.50/0.99  
% 3.50/0.99  fof(f14,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/0.99    inference(ennf_transformation,[],[f12])).
% 3.50/0.99  
% 3.50/0.99  fof(f47,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f14])).
% 3.50/0.99  
% 3.50/0.99  fof(f4,axiom,(
% 3.50/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f13,plain,(
% 3.50/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.50/0.99    inference(ennf_transformation,[],[f4])).
% 3.50/0.99  
% 3.50/0.99  fof(f27,plain,(
% 3.50/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.50/0.99    inference(nnf_transformation,[],[f13])).
% 3.50/0.99  
% 3.50/0.99  fof(f45,plain,(
% 3.50/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f27])).
% 3.50/0.99  
% 3.50/0.99  fof(f53,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f28])).
% 3.50/0.99  
% 3.50/0.99  fof(f79,plain,(
% 3.50/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.50/0.99    inference(equality_resolution,[],[f53])).
% 3.50/0.99  
% 3.50/0.99  fof(f43,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.50/0.99    inference(cnf_transformation,[],[f26])).
% 3.50/0.99  
% 3.50/0.99  fof(f75,plain,(
% 3.50/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.50/0.99    inference(equality_resolution,[],[f43])).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.50/0.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.50/0.99      | ~ v1_relat_1(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6568,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.50/0.99      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.50/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.50/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1,plain,
% 3.50/0.99      ( r1_tarski(X0,X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6571,plain,
% 3.50/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_33,negated_conjecture,
% 3.50/0.99      ( r2_hidden(sK6,k1_funct_2(sK4,sK5)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6553,plain,
% 3.50/0.99      ( r2_hidden(sK6,k1_funct_2(sK4,sK5)) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_31,plain,
% 3.50/0.99      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6554,plain,
% 3.50/0.99      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_27,plain,
% 3.50/0.99      ( ~ sP0(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK3(X0,X1,X3) = X3 ),
% 3.50/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6558,plain,
% 3.50/0.99      ( sK3(X0,X1,X2) = X2
% 3.50/0.99      | sP0(X0,X1,X3) != iProver_top
% 3.50/0.99      | r2_hidden(X2,X3) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7407,plain,
% 3.50/0.99      ( sK3(X0,X1,X2) = X2
% 3.50/0.99      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_6554,c_6558]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7412,plain,
% 3.50/0.99      ( sK3(sK5,sK4,sK6) = sK6 ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_6553,c_7407]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_25,plain,
% 3.50/0.99      ( ~ sP0(X0,X1,X2)
% 3.50/0.99      | ~ r2_hidden(X3,X2)
% 3.50/0.99      | r1_tarski(k2_relat_1(sK3(X0,X1,X3)),X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6560,plain,
% 3.50/0.99      ( sP0(X0,X1,X2) != iProver_top
% 3.50/0.99      | r2_hidden(X3,X2) != iProver_top
% 3.50/0.99      | r1_tarski(k2_relat_1(sK3(X0,X1,X3)),X0) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8120,plain,
% 3.50/0.99      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 3.50/0.99      | r1_tarski(k2_relat_1(sK3(X2,X1,X0)),X2) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_6554,c_6560]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8772,plain,
% 3.50/0.99      ( r2_hidden(sK6,k1_funct_2(sK4,sK5)) != iProver_top
% 3.50/0.99      | r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_7412,c_8120]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_34,plain,
% 3.50/0.99      ( r2_hidden(sK6,k1_funct_2(sK4,sK5)) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8800,plain,
% 3.50/0.99      ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_8772,c_34]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6569,plain,
% 3.50/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.50/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9072,plain,
% 3.50/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.50/0.99      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.50/0.99      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.50/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_6568,c_6569]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10773,plain,
% 3.50/0.99      ( k1_relset_1(X0,sK5,sK6) = k1_relat_1(sK6)
% 3.50/0.99      | r1_tarski(k1_relat_1(sK6),X0) != iProver_top
% 3.50/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_8800,c_9072]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_26,plain,
% 3.50/0.99      ( ~ sP0(X0,X1,X2)
% 3.50/0.99      | ~ r2_hidden(X3,X2)
% 3.50/0.99      | k1_relat_1(sK3(X0,X1,X3)) = X1 ),
% 3.50/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6559,plain,
% 3.50/0.99      ( k1_relat_1(sK3(X0,X1,X2)) = X1
% 3.50/0.99      | sP0(X0,X1,X3) != iProver_top
% 3.50/0.99      | r2_hidden(X2,X3) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7768,plain,
% 3.50/0.99      ( k1_relat_1(sK3(X0,X1,X2)) = X1
% 3.50/0.99      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_6554,c_6559]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8044,plain,
% 3.50/0.99      ( k1_relat_1(sK3(sK5,sK4,sK6)) = sK4 ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_6553,c_7768]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8045,plain,
% 3.50/0.99      ( k1_relat_1(sK6) = sK4 ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_8044,c_7412]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10777,plain,
% 3.50/0.99      ( k1_relset_1(X0,sK5,sK6) = sK4
% 3.50/0.99      | r1_tarski(sK4,X0) != iProver_top
% 3.50/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_10773,c_8045]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_29,plain,
% 3.50/0.99      ( ~ sP0(X0,X1,X2)
% 3.50/0.99      | ~ r2_hidden(X3,X2)
% 3.50/0.99      | v1_relat_1(sK3(X0,X1,X3)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6556,plain,
% 3.50/0.99      ( sP0(X0,X1,X2) != iProver_top
% 3.50/0.99      | r2_hidden(X3,X2) != iProver_top
% 3.50/0.99      | v1_relat_1(sK3(X0,X1,X3)) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7656,plain,
% 3.50/0.99      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 3.50/0.99      | v1_relat_1(sK3(X2,X1,X0)) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_6554,c_6556]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7871,plain,
% 3.50/0.99      ( v1_relat_1(sK3(sK5,sK4,sK6)) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_6553,c_7656]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7872,plain,
% 3.50/0.99      ( v1_relat_1(sK6) = iProver_top ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_7871,c_7412]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11004,plain,
% 3.50/0.99      ( r1_tarski(sK4,X0) != iProver_top
% 3.50/0.99      | k1_relset_1(X0,sK5,sK6) = sK4 ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_10777,c_7872]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11005,plain,
% 3.50/0.99      ( k1_relset_1(X0,sK5,sK6) = sK4
% 3.50/0.99      | r1_tarski(sK4,X0) != iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_11004]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11012,plain,
% 3.50/0.99      ( k1_relset_1(sK4,sK5,sK6) = sK4 ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_6571,c_11005]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_15,plain,
% 3.50/0.99      ( v1_funct_2(X0,X1,X2)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.50/0.99      | k1_xboole_0 = X2 ),
% 3.50/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_32,negated_conjecture,
% 3.50/0.99      ( ~ v1_funct_2(sK6,sK4,sK5)
% 3.50/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.50/0.99      | ~ v1_funct_1(sK6) ),
% 3.50/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1072,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.50/0.99      | ~ v1_funct_1(sK6)
% 3.50/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.50/0.99      | sK5 != X2
% 3.50/0.99      | sK4 != X1
% 3.50/0.99      | sK6 != X0
% 3.50/0.99      | k1_xboole_0 = X2 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1073,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.50/0.99      | ~ v1_funct_1(sK6)
% 3.50/0.99      | k1_relset_1(sK4,sK5,sK6) != sK4
% 3.50/0.99      | k1_xboole_0 = sK5 ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_1072]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6549,plain,
% 3.50/0.99      ( k1_relset_1(sK4,sK5,sK6) != sK4
% 3.50/0.99      | k1_xboole_0 = sK5
% 3.50/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.50/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1073]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11221,plain,
% 3.50/0.99      ( sK5 = k1_xboole_0
% 3.50/0.99      | sK4 != sK4
% 3.50/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.50/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_11012,c_6549]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11223,plain,
% 3.50/0.99      ( sK5 = k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.50/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.50/0.99      inference(equality_resolution_simp,[status(thm)],[c_11221]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_28,plain,
% 3.50/0.99      ( ~ sP0(X0,X1,X2)
% 3.50/0.99      | ~ r2_hidden(X3,X2)
% 3.50/0.99      | v1_funct_1(sK3(X0,X1,X3)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6557,plain,
% 3.50/0.99      ( sP0(X0,X1,X2) != iProver_top
% 3.50/0.99      | r2_hidden(X3,X2) != iProver_top
% 3.50/0.99      | v1_funct_1(sK3(X0,X1,X3)) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7662,plain,
% 3.50/0.99      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 3.50/0.99      | v1_funct_1(sK3(X2,X1,X0)) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_6554,c_6557]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7975,plain,
% 3.50/0.99      ( v1_funct_1(sK3(sK5,sK4,sK6)) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_6553,c_7662]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7976,plain,
% 3.50/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_7975,c_7412]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6101,plain,( X0 = X0 ),theory(equality) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10415,plain,
% 3.50/0.99      ( sK4 = sK4 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_6101]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11225,plain,
% 3.50/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.50/0.99      | sK5 = k1_xboole_0 ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_11223,c_7976,c_10415,c_11221]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11226,plain,
% 3.50/0.99      ( sK5 = k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_11225]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11231,plain,
% 3.50/0.99      ( sK5 = k1_xboole_0
% 3.50/0.99      | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
% 3.50/0.99      | r1_tarski(k1_relat_1(sK6),sK4) != iProver_top
% 3.50/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_6568,c_11226]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11232,plain,
% 3.50/0.99      ( sK5 = k1_xboole_0
% 3.50/0.99      | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
% 3.50/0.99      | r1_tarski(sK4,sK4) != iProver_top
% 3.50/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_11231,c_8045]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8956,plain,
% 3.50/0.99      ( r1_tarski(sK4,sK4) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8959,plain,
% 3.50/0.99      ( r1_tarski(sK4,sK4) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_8956]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11391,plain,
% 3.50/0.99      ( sK5 = k1_xboole_0 ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_11232,c_34,c_7872,c_8772,c_8959]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11402,plain,
% 3.50/0.99      ( r2_hidden(sK6,k1_funct_2(sK4,k1_xboole_0)) = iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_11391,c_6553]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3,plain,
% 3.50/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6570,plain,
% 3.50/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_0,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.50/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6572,plain,
% 3.50/0.99      ( X0 = X1
% 3.50/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.50/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7339,plain,
% 3.50/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_6570,c_6572]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8775,plain,
% 3.50/0.99      ( k2_relat_1(sK3(k1_xboole_0,X0,X1)) = k1_xboole_0
% 3.50/0.99      | r2_hidden(X1,k1_funct_2(X0,k1_xboole_0)) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_8120,c_7339]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11460,plain,
% 3.50/0.99      ( k2_relat_1(sK3(k1_xboole_0,sK4,sK6)) = k1_xboole_0 ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_11402,c_8775]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11399,plain,
% 3.50/0.99      ( sK3(k1_xboole_0,sK4,sK6) = sK6 ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_11391,c_7412]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_12485,plain,
% 3.50/0.99      ( k2_relat_1(sK6) = k1_xboole_0 ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_11460,c_11399]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4,plain,
% 3.50/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9070,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.50/0.99      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.50/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.50/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_4,c_6568]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9239,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.50/0.99      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.50/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_6571,c_9070]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_12525,plain,
% 3.50/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.50/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.50/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_12485,c_9239]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_113,plain,
% 3.50/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_115,plain,
% 3.50/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_113]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_13380,plain,
% 3.50/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_12525,c_115,c_7872]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | v4_relat_1(X0,X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8,plain,
% 3.50/0.99      ( ~ v4_relat_1(X0,X1)
% 3.50/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.50/0.99      | ~ v1_relat_1(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_354,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.50/0.99      | ~ v1_relat_1(X0) ),
% 3.50/0.99      inference(resolution,[status(thm)],[c_9,c_8]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6552,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.50/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.50/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7505,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.50/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.50/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_4,c_6552]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_13385,plain,
% 3.50/0.99      ( r1_tarski(k1_relat_1(sK6),X0) = iProver_top
% 3.50/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_13380,c_7505]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_13396,plain,
% 3.50/0.99      ( r1_tarski(sK4,X0) = iProver_top
% 3.50/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_13385,c_8045]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_13487,plain,
% 3.50/0.99      ( r1_tarski(sK4,X0) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_13396,c_7872]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_13495,plain,
% 3.50/0.99      ( sK4 = k1_xboole_0 ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_13487,c_7339]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7018,plain,
% 3.50/0.99      ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
% 3.50/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_4,c_6569]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_13387,plain,
% 3.50/0.99      ( k1_relset_1(X0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_13380,c_7018]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_13389,plain,
% 3.50/0.99      ( k1_relset_1(X0,k1_xboole_0,sK6) = sK4 ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_13387,c_8045]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_14,plain,
% 3.50/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.50/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1053,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.50/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.50/0.99      | ~ v1_funct_1(sK6)
% 3.50/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.50/0.99      | sK5 != X1
% 3.50/0.99      | sK4 != k1_xboole_0
% 3.50/0.99      | sK6 != X0 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_32]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1054,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.50/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
% 3.50/0.99      | ~ v1_funct_1(sK6)
% 3.50/0.99      | k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
% 3.50/0.99      | sK4 != k1_xboole_0 ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_1053]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6550,plain,
% 3.50/0.99      ( k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
% 3.50/0.99      | sK4 != k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.50/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top
% 3.50/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1054]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_5,plain,
% 3.50/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6697,plain,
% 3.50/0.99      ( k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
% 3.50/0.99      | sK4 != k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.50/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.50/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_6550,c_5]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11401,plain,
% 3.50/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) != k1_xboole_0
% 3.50/0.99      | sK4 != k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top
% 3.50/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.50/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_11391,c_6697]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11410,plain,
% 3.50/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) != k1_xboole_0
% 3.50/0.99      | sK4 != k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.50/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_11401,c_4]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_114,plain,
% 3.50/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7977,plain,
% 3.50/0.99      ( v1_funct_1(sK6) ),
% 3.50/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_7976]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6103,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.50/0.99      theory(equality) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8961,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,X1) | sK4 != X0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_6103]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8963,plain,
% 3.50/0.99      ( r1_tarski(sK4,k1_xboole_0)
% 3.50/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.50/0.99      | sK4 != k1_xboole_0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_8961]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9071,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.50/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.50/0.99      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 3.50/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_5,c_6568]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9272,plain,
% 3.50/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.50/0.99      | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top
% 3.50/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_8800,c_9071]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9568,plain,
% 3.50/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.50/0.99      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.50/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_9272,c_8045]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9612,plain,
% 3.50/0.99      ( r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.50/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_9568,c_7872]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9613,plain,
% 3.50/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.50/0.99      | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_9612]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9614,plain,
% 3.50/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0))
% 3.50/0.99      | ~ r1_tarski(sK4,k1_xboole_0) ),
% 3.50/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_9613]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11452,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0))
% 3.50/0.99      | ~ v1_funct_1(sK6)
% 3.50/0.99      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) != k1_xboole_0
% 3.50/0.99      | sK4 != k1_xboole_0 ),
% 3.50/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_11410]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11890,plain,
% 3.50/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) != k1_xboole_0
% 3.50/0.99      | sK4 != k1_xboole_0 ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_11410,c_114,c_7977,c_8963,c_9614,c_11452]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_13404,plain,
% 3.50/0.99      ( sK4 != k1_xboole_0 ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_13389,c_11890]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(contradiction,plain,
% 3.50/0.99      ( $false ),
% 3.50/0.99      inference(minisat,[status(thm)],[c_13495,c_13404]) ).
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  ------                               Statistics
% 3.50/0.99  
% 3.50/0.99  ------ General
% 3.50/0.99  
% 3.50/0.99  abstr_ref_over_cycles:                  0
% 3.50/0.99  abstr_ref_under_cycles:                 0
% 3.50/0.99  gc_basic_clause_elim:                   0
% 3.50/0.99  forced_gc_time:                         0
% 3.50/0.99  parsing_time:                           0.009
% 3.50/0.99  unif_index_cands_time:                  0.
% 3.50/0.99  unif_index_add_time:                    0.
% 3.50/0.99  orderings_time:                         0.
% 3.50/0.99  out_proof_time:                         0.01
% 3.50/0.99  total_time:                             0.281
% 3.50/0.99  num_of_symbols:                         52
% 3.50/0.99  num_of_terms:                           9203
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing
% 3.50/0.99  
% 3.50/0.99  num_of_splits:                          0
% 3.50/0.99  num_of_split_atoms:                     0
% 3.50/0.99  num_of_reused_defs:                     0
% 3.50/0.99  num_eq_ax_congr_red:                    34
% 3.50/0.99  num_of_sem_filtered_clauses:            1
% 3.50/0.99  num_of_subtypes:                        0
% 3.50/0.99  monotx_restored_types:                  0
% 3.50/0.99  sat_num_of_epr_types:                   0
% 3.50/0.99  sat_num_of_non_cyclic_types:            0
% 3.50/0.99  sat_guarded_non_collapsed_types:        0
% 3.50/0.99  num_pure_diseq_elim:                    0
% 3.50/0.99  simp_replaced_by:                       0
% 3.50/0.99  res_preprocessed:                       145
% 3.50/0.99  prep_upred:                             0
% 3.50/0.99  prep_unflattend:                        323
% 3.50/0.99  smt_new_axioms:                         0
% 3.50/0.99  pred_elim_cands:                        6
% 3.50/0.99  pred_elim:                              2
% 3.50/0.99  pred_elim_cl:                           6
% 3.50/0.99  pred_elim_cycles:                       12
% 3.50/0.99  merged_defs:                            0
% 3.50/0.99  merged_defs_ncl:                        0
% 3.50/0.99  bin_hyper_res:                          0
% 3.50/0.99  prep_cycles:                            4
% 3.50/0.99  pred_elim_time:                         0.073
% 3.50/0.99  splitting_time:                         0.
% 3.50/0.99  sem_filter_time:                        0.
% 3.50/0.99  monotx_time:                            0.
% 3.50/0.99  subtype_inf_time:                       0.
% 3.50/0.99  
% 3.50/0.99  ------ Problem properties
% 3.50/0.99  
% 3.50/0.99  clauses:                                27
% 3.50/0.99  conjectures:                            1
% 3.50/0.99  epr:                                    3
% 3.50/0.99  horn:                                   21
% 3.50/0.99  ground:                                 4
% 3.50/0.99  unary:                                  6
% 3.50/0.99  binary:                                 2
% 3.50/0.99  lits:                                   79
% 3.50/0.99  lits_eq:                                20
% 3.50/0.99  fd_pure:                                0
% 3.50/0.99  fd_pseudo:                              0
% 3.50/0.99  fd_cond:                                1
% 3.50/0.99  fd_pseudo_cond:                         2
% 3.50/0.99  ac_symbols:                             0
% 3.50/0.99  
% 3.50/0.99  ------ Propositional Solver
% 3.50/0.99  
% 3.50/0.99  prop_solver_calls:                      30
% 3.50/0.99  prop_fast_solver_calls:                 2365
% 3.50/0.99  smt_solver_calls:                       0
% 3.50/0.99  smt_fast_solver_calls:                  0
% 3.50/0.99  prop_num_of_clauses:                    3406
% 3.50/0.99  prop_preprocess_simplified:             10039
% 3.50/0.99  prop_fo_subsumed:                       42
% 3.50/0.99  prop_solver_time:                       0.
% 3.50/0.99  smt_solver_time:                        0.
% 3.50/0.99  smt_fast_solver_time:                   0.
% 3.50/0.99  prop_fast_solver_time:                  0.
% 3.50/0.99  prop_unsat_core_time:                   0.
% 3.50/0.99  
% 3.50/0.99  ------ QBF
% 3.50/0.99  
% 3.50/0.99  qbf_q_res:                              0
% 3.50/0.99  qbf_num_tautologies:                    0
% 3.50/0.99  qbf_prep_cycles:                        0
% 3.50/0.99  
% 3.50/0.99  ------ BMC1
% 3.50/0.99  
% 3.50/0.99  bmc1_current_bound:                     -1
% 3.50/0.99  bmc1_last_solved_bound:                 -1
% 3.50/0.99  bmc1_unsat_core_size:                   -1
% 3.50/0.99  bmc1_unsat_core_parents_size:           -1
% 3.50/0.99  bmc1_merge_next_fun:                    0
% 3.50/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.50/0.99  
% 3.50/0.99  ------ Instantiation
% 3.50/0.99  
% 3.50/0.99  inst_num_of_clauses:                    815
% 3.50/0.99  inst_num_in_passive:                    419
% 3.50/0.99  inst_num_in_active:                     311
% 3.50/0.99  inst_num_in_unprocessed:                90
% 3.50/0.99  inst_num_of_loops:                      470
% 3.50/0.99  inst_num_of_learning_restarts:          0
% 3.50/0.99  inst_num_moves_active_passive:          154
% 3.50/0.99  inst_lit_activity:                      0
% 3.50/0.99  inst_lit_activity_moves:                0
% 3.50/0.99  inst_num_tautologies:                   0
% 3.50/0.99  inst_num_prop_implied:                  0
% 3.50/0.99  inst_num_existing_simplified:           0
% 3.50/0.99  inst_num_eq_res_simplified:             0
% 3.50/0.99  inst_num_child_elim:                    0
% 3.50/0.99  inst_num_of_dismatching_blockings:      591
% 3.50/0.99  inst_num_of_non_proper_insts:           807
% 3.50/0.99  inst_num_of_duplicates:                 0
% 3.50/0.99  inst_inst_num_from_inst_to_res:         0
% 3.50/0.99  inst_dismatching_checking_time:         0.
% 3.50/0.99  
% 3.50/0.99  ------ Resolution
% 3.50/0.99  
% 3.50/0.99  res_num_of_clauses:                     0
% 3.50/0.99  res_num_in_passive:                     0
% 3.50/0.99  res_num_in_active:                      0
% 3.50/0.99  res_num_of_loops:                       149
% 3.50/0.99  res_forward_subset_subsumed:            30
% 3.50/0.99  res_backward_subset_subsumed:           12
% 3.50/0.99  res_forward_subsumed:                   0
% 3.50/0.99  res_backward_subsumed:                  0
% 3.50/0.99  res_forward_subsumption_resolution:     2
% 3.50/0.99  res_backward_subsumption_resolution:    0
% 3.50/0.99  res_clause_to_clause_subsumption:       847
% 3.50/0.99  res_orphan_elimination:                 0
% 3.50/0.99  res_tautology_del:                      40
% 3.50/0.99  res_num_eq_res_simplified:              0
% 3.50/0.99  res_num_sel_changes:                    0
% 3.50/0.99  res_moves_from_active_to_pass:          0
% 3.50/0.99  
% 3.50/0.99  ------ Superposition
% 3.50/0.99  
% 3.50/0.99  sup_time_total:                         0.
% 3.50/0.99  sup_time_generating:                    0.
% 3.50/0.99  sup_time_sim_full:                      0.
% 3.50/0.99  sup_time_sim_immed:                     0.
% 3.50/0.99  
% 3.50/0.99  sup_num_of_clauses:                     128
% 3.50/0.99  sup_num_in_active:                      68
% 3.50/0.99  sup_num_in_passive:                     60
% 3.50/0.99  sup_num_of_loops:                       93
% 3.50/0.99  sup_fw_superposition:                   59
% 3.50/0.99  sup_bw_superposition:                   86
% 3.50/0.99  sup_immediate_simplified:               35
% 3.50/0.99  sup_given_eliminated:                   3
% 3.50/0.99  comparisons_done:                       0
% 3.50/0.99  comparisons_avoided:                    3
% 3.50/0.99  
% 3.50/0.99  ------ Simplifications
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  sim_fw_subset_subsumed:                 2
% 3.50/0.99  sim_bw_subset_subsumed:                 10
% 3.50/0.99  sim_fw_subsumed:                        11
% 3.50/0.99  sim_bw_subsumed:                        6
% 3.50/0.99  sim_fw_subsumption_res:                 2
% 3.50/0.99  sim_bw_subsumption_res:                 0
% 3.50/0.99  sim_tautology_del:                      1
% 3.50/0.99  sim_eq_tautology_del:                   8
% 3.50/0.99  sim_eq_res_simp:                        2
% 3.50/0.99  sim_fw_demodulated:                     4
% 3.50/0.99  sim_bw_demodulated:                     21
% 3.50/0.99  sim_light_normalised:                   38
% 3.50/0.99  sim_joinable_taut:                      0
% 3.50/0.99  sim_joinable_simp:                      0
% 3.50/0.99  sim_ac_normalised:                      0
% 3.50/0.99  sim_smt_subsumption:                    0
% 3.50/0.99  
%------------------------------------------------------------------------------

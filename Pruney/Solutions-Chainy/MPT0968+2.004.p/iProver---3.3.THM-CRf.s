%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:44 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  192 (6740 expanded)
%              Number of clauses        :  113 (2158 expanded)
%              Number of leaves         :   21 (1369 expanded)
%              Depth                    :   29
%              Number of atoms          :  646 (34612 expanded)
%              Number of equality atoms :  313 (13454 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
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

fof(f38,plain,(
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

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f17,f38])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f150,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f119])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f135,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f67,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(sK10,k1_funct_2(sK8,sK9))
      & ( k1_xboole_0 = sK8
        | k1_xboole_0 != sK9 )
      & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
      & v1_funct_2(sK10,sK8,sK9)
      & v1_funct_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ~ r2_hidden(sK10,k1_funct_2(sK8,sK9))
    & ( k1_xboole_0 = sK8
      | k1_xboole_0 != sK9 )
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    & v1_funct_2(sK10,sK8,sK9)
    & v1_funct_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f37,f67])).

fof(f130,plain,(
    v1_funct_2(sK10,sK8,sK9) ),
    inference(cnf_transformation,[],[f68])).

fof(f131,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
    inference(cnf_transformation,[],[f68])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f59,plain,(
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
    inference(rectify,[],[f58])).

fof(f62,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X0)
          & k1_relat_1(X8) = X1
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X0)
        & k1_relat_1(sK6(X0,X1,X6)) = X1
        & sK6(X0,X1,X6) = X6
        & v1_funct_1(sK6(X0,X1,X6))
        & v1_relat_1(sK6(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X0)
          & k1_relat_1(X5) = X1
          & X3 = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X0)
        & k1_relat_1(sK5(X0,X1,X2)) = X1
        & sK5(X0,X1,X2) = X3
        & v1_funct_1(sK5(X0,X1,X2))
        & v1_relat_1(sK5(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
              | sK4(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X0)
              & k1_relat_1(X5) = X1
              & sK4(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | k1_relat_1(X4) != X1
                | sK4(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X0)
              & k1_relat_1(sK5(X0,X1,X2)) = X1
              & sK4(X0,X1,X2) = sK5(X0,X1,X2)
              & v1_funct_1(sK5(X0,X1,X2))
              & v1_relat_1(sK5(X0,X1,X2)) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | k1_relat_1(X7) != X1
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X0)
                & k1_relat_1(sK6(X0,X1,X6)) = X1
                & sK6(X0,X1,X6) = X6
                & v1_funct_1(sK6(X0,X1,X6))
                & v1_relat_1(sK6(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f59,f62,f61,f60])).

fof(f112,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_tarski(k2_relat_1(X7),X0)
      | k1_relat_1(X7) != X1
      | X6 != X7
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f148,plain,(
    ! [X6,X2,X0,X7] :
      ( r2_hidden(X6,X2)
      | ~ r1_tarski(k2_relat_1(X7),X0)
      | X6 != X7
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | ~ sP0(X0,k1_relat_1(X7),X2) ) ),
    inference(equality_resolution,[],[f112])).

fof(f149,plain,(
    ! [X2,X0,X7] :
      ( r2_hidden(X7,X2)
      | ~ r1_tarski(k2_relat_1(X7),X0)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | ~ sP0(X0,k1_relat_1(X7),X2) ) ),
    inference(equality_resolution,[],[f148])).

fof(f129,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f68])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f133,plain,(
    ~ r2_hidden(sK10,k1_funct_2(sK8,sK9)) ),
    inference(cnf_transformation,[],[f68])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f132,plain,
    ( k1_xboole_0 = sK8
    | k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f68])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f146,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f102])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f137,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f127,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f128,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_51,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_7117,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_7146,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_37,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_63,negated_conjecture,
    ( v1_funct_2(sK10,sK8,sK9) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_920,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK9 != X2
    | sK8 != X1
    | sK10 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_63])).

cnf(c_921,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | k1_relset_1(sK8,sK9,sK10) = sK8
    | k1_xboole_0 = sK9 ),
    inference(unflattening,[status(thm)],[c_920])).

cnf(c_62,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_923,plain,
    ( k1_relset_1(sK8,sK9,sK10) = sK8
    | k1_xboole_0 = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_921,c_62])).

cnf(c_7111,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_7132,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10005,plain,
    ( k1_relset_1(sK8,sK9,sK10) = k1_relat_1(sK10) ),
    inference(superposition,[status(thm)],[c_7111,c_7132])).

cnf(c_10067,plain,
    ( k1_relat_1(sK10) = sK8
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_923,c_10005])).

cnf(c_44,plain,
    ( ~ sP0(X0,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X0)
    | r2_hidden(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_7124,plain,
    ( sP0(X0,k1_relat_1(X1),X2) != iProver_top
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_12072,plain,
    ( sK9 = k1_xboole_0
    | sP0(X0,sK8,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK10),X0) != iProver_top
    | r2_hidden(sK10,X1) = iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_10067,c_7124])).

cnf(c_64,negated_conjecture,
    ( v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_65,plain,
    ( v1_funct_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_67,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_7535,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_7536,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) != iProver_top
    | v1_relat_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7535])).

cnf(c_12528,plain,
    ( sK9 = k1_xboole_0
    | sP0(X0,sK8,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK10),X0) != iProver_top
    | r2_hidden(sK10,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12072,c_65,c_67,c_7536])).

cnf(c_12539,plain,
    ( sK9 = k1_xboole_0
    | sP0(k2_relat_1(sK10),sK8,X0) != iProver_top
    | r2_hidden(sK10,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7146,c_12528])).

cnf(c_60,negated_conjecture,
    ( ~ r2_hidden(sK10,k1_funct_2(sK8,sK9)) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_68,plain,
    ( r2_hidden(sK10,k1_funct_2(sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_7131,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_9815,plain,
    ( k2_relset_1(sK8,sK9,sK10) = k2_relat_1(sK10) ),
    inference(superposition,[status(thm)],[c_7111,c_7131])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_7133,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_10945,plain,
    ( m1_subset_1(k2_relat_1(sK10),k1_zfmisc_1(sK9)) = iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9815,c_7133])).

cnf(c_11158,plain,
    ( m1_subset_1(k2_relat_1(sK10),k1_zfmisc_1(sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10945,c_67])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_7143,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11163,plain,
    ( r1_tarski(k2_relat_1(sK10),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_11158,c_7143])).

cnf(c_12540,plain,
    ( sK9 = k1_xboole_0
    | sP0(sK9,sK8,X0) != iProver_top
    | r2_hidden(sK10,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11163,c_12528])).

cnf(c_12574,plain,
    ( sK9 = k1_xboole_0
    | r2_hidden(sK10,k1_funct_2(sK8,sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7117,c_12540])).

cnf(c_12756,plain,
    ( sK9 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12539,c_68,c_12574])).

cnf(c_12771,plain,
    ( k1_relset_1(sK8,k1_xboole_0,sK10) = k1_relat_1(sK10) ),
    inference(demodulation,[status(thm)],[c_12756,c_10005])).

cnf(c_61,negated_conjecture,
    ( k1_xboole_0 != sK9
    | k1_xboole_0 = sK8 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_12779,plain,
    ( sK8 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12756,c_61])).

cnf(c_12780,plain,
    ( sK8 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_12779])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f146])).

cnf(c_883,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK9 != X1
    | sK8 != k1_xboole_0
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_63])).

cnf(c_884,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK9)))
    | k1_relset_1(k1_xboole_0,sK9,sK10) = k1_xboole_0
    | sK8 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_883])).

cnf(c_7104,plain,
    ( k1_relset_1(k1_xboole_0,sK9,sK10) = k1_xboole_0
    | sK8 != k1_xboole_0
    | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_884])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f137])).

cnf(c_7281,plain,
    ( k1_relset_1(k1_xboole_0,sK9,sK10) = k1_xboole_0
    | sK8 != k1_xboole_0
    | m1_subset_1(sK10,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7104,c_10])).

cnf(c_12775,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK10) = k1_xboole_0
    | sK8 != k1_xboole_0
    | m1_subset_1(sK10,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12756,c_7281])).

cnf(c_12790,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK10) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK10,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12775,c_12780])).

cnf(c_12791,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK10) = k1_xboole_0
    | m1_subset_1(sK10,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_12790])).

cnf(c_12778,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12756,c_7111])).

cnf(c_12783,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12778,c_12780])).

cnf(c_12785,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12783,c_10])).

cnf(c_12794,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK10) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12791,c_12785])).

cnf(c_12804,plain,
    ( k1_relat_1(sK10) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12771,c_12780,c_12794])).

cnf(c_12951,plain,
    ( sP0(X0,k1_xboole_0,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK10),X0) != iProver_top
    | r2_hidden(sK10,X1) = iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_12804,c_7124])).

cnf(c_13952,plain,
    ( sP0(X0,k1_xboole_0,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK10),X0) != iProver_top
    | r2_hidden(sK10,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12951,c_65,c_67,c_7536])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_7149,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_7151,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9093,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7149,c_7151])).

cnf(c_8640,plain,
    ( r1_tarski(sK10,k2_zfmisc_1(sK8,sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7111,c_7143])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_7147,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10865,plain,
    ( k2_zfmisc_1(sK8,sK9) = sK10
    | r1_tarski(k2_zfmisc_1(sK8,sK9),sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_8640,c_7147])).

cnf(c_11155,plain,
    ( k2_zfmisc_1(sK8,sK9) = sK10
    | v1_xboole_0(k2_zfmisc_1(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9093,c_10865])).

cnf(c_12767,plain,
    ( k2_zfmisc_1(sK8,k1_xboole_0) = sK10
    | v1_xboole_0(k2_zfmisc_1(sK8,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12756,c_11155])).

cnf(c_12817,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK10
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12767,c_12780])).

cnf(c_12820,plain,
    ( sK10 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12817,c_10])).

cnf(c_8611,plain,
    ( ~ r1_tarski(X0,sK10)
    | ~ r1_tarski(sK10,X0)
    | sK10 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8612,plain,
    ( sK10 = X0
    | r1_tarski(X0,sK10) != iProver_top
    | r1_tarski(sK10,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8611])).

cnf(c_8614,plain,
    ( sK10 = k1_xboole_0
    | r1_tarski(sK10,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK10) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8612])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_9039,plain,
    ( r1_tarski(k1_xboole_0,sK10) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9042,plain,
    ( r1_tarski(k1_xboole_0,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9039])).

cnf(c_11987,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(X0))
    | r1_tarski(sK10,X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_11988,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK10,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11987])).

cnf(c_11990,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK10,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11988])).

cnf(c_13514,plain,
    ( sK10 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12820,c_8614,c_9042,c_11990,c_12785])).

cnf(c_7110,plain,
    ( v1_funct_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_58,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_896,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | k1_relset_1(X1,X2,X0) = X1
    | k2_relat_1(X3) != X2
    | k1_relat_1(X3) != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_58])).

cnf(c_897,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_896])).

cnf(c_57,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_901,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_897,c_57])).

cnf(c_7103,plain,
    ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k1_xboole_0 = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_901])).

cnf(c_7624,plain,
    ( k1_relset_1(k1_relat_1(sK10),k2_relat_1(sK10),sK10) = k1_relat_1(sK10)
    | k2_relat_1(sK10) = k1_xboole_0
    | v1_relat_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_7110,c_7103])).

cnf(c_2113,plain,
    ( ~ v1_relat_1(X0)
    | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_901,c_64])).

cnf(c_2114,plain,
    ( ~ v1_relat_1(sK10)
    | k1_relset_1(k1_relat_1(sK10),k2_relat_1(sK10),sK10) = k1_relat_1(sK10)
    | k2_relat_1(sK10) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_2113])).

cnf(c_7657,plain,
    ( k2_relat_1(sK10) = k1_xboole_0
    | k1_relset_1(k1_relat_1(sK10),k2_relat_1(sK10),sK10) = k1_relat_1(sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7624,c_62,c_2114,c_7535])).

cnf(c_7658,plain,
    ( k1_relset_1(k1_relat_1(sK10),k2_relat_1(sK10),sK10) = k1_relat_1(sK10)
    | k2_relat_1(sK10) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7657])).

cnf(c_12949,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK10),sK10) = k1_xboole_0
    | k2_relat_1(sK10) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12804,c_7658])).

cnf(c_9232,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK10)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9235,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9232])).

cnf(c_11240,plain,
    ( k2_relat_1(sK10) = sK9
    | r1_tarski(sK9,k2_relat_1(sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11163,c_7147])).

cnf(c_12766,plain,
    ( k2_relat_1(sK10) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(sK10)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12756,c_11240])).

cnf(c_13630,plain,
    ( k2_relat_1(sK10) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12949,c_9235,c_12766])).

cnf(c_13632,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_13630,c_13514])).

cnf(c_13958,plain,
    ( sP0(X0,k1_xboole_0,X1) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | r2_hidden(k1_xboole_0,X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13952,c_13514,c_13632])).

cnf(c_7145,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_13962,plain,
    ( sP0(X0,k1_xboole_0,X1) != iProver_top
    | r2_hidden(k1_xboole_0,X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13958,c_7145])).

cnf(c_13966,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7117,c_13962])).

cnf(c_13968,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_13966])).

cnf(c_7112,plain,
    ( r2_hidden(sK10,k1_funct_2(sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_12777,plain,
    ( r2_hidden(sK10,k1_funct_2(sK8,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12756,c_7112])).

cnf(c_12787,plain,
    ( r2_hidden(sK10,k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12777,c_12780])).

cnf(c_13520,plain,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13514,c_12787])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13968,c_13520])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.26/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.00  
% 3.26/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.26/1.00  
% 3.26/1.00  ------  iProver source info
% 3.26/1.00  
% 3.26/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.26/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.26/1.00  git: non_committed_changes: false
% 3.26/1.00  git: last_make_outside_of_git: false
% 3.26/1.00  
% 3.26/1.00  ------ 
% 3.26/1.00  
% 3.26/1.00  ------ Input Options
% 3.26/1.00  
% 3.26/1.00  --out_options                           all
% 3.26/1.00  --tptp_safe_out                         true
% 3.26/1.00  --problem_path                          ""
% 3.26/1.00  --include_path                          ""
% 3.26/1.00  --clausifier                            res/vclausify_rel
% 3.26/1.00  --clausifier_options                    --mode clausify
% 3.26/1.00  --stdin                                 false
% 3.26/1.00  --stats_out                             all
% 3.26/1.00  
% 3.26/1.00  ------ General Options
% 3.26/1.00  
% 3.26/1.00  --fof                                   false
% 3.26/1.00  --time_out_real                         305.
% 3.26/1.00  --time_out_virtual                      -1.
% 3.26/1.00  --symbol_type_check                     false
% 3.26/1.00  --clausify_out                          false
% 3.26/1.00  --sig_cnt_out                           false
% 3.26/1.00  --trig_cnt_out                          false
% 3.26/1.00  --trig_cnt_out_tolerance                1.
% 3.26/1.00  --trig_cnt_out_sk_spl                   false
% 3.26/1.00  --abstr_cl_out                          false
% 3.26/1.00  
% 3.26/1.00  ------ Global Options
% 3.26/1.00  
% 3.26/1.00  --schedule                              default
% 3.26/1.00  --add_important_lit                     false
% 3.26/1.00  --prop_solver_per_cl                    1000
% 3.26/1.00  --min_unsat_core                        false
% 3.26/1.00  --soft_assumptions                      false
% 3.26/1.00  --soft_lemma_size                       3
% 3.26/1.00  --prop_impl_unit_size                   0
% 3.26/1.00  --prop_impl_unit                        []
% 3.26/1.00  --share_sel_clauses                     true
% 3.26/1.00  --reset_solvers                         false
% 3.26/1.00  --bc_imp_inh                            [conj_cone]
% 3.26/1.00  --conj_cone_tolerance                   3.
% 3.26/1.00  --extra_neg_conj                        none
% 3.26/1.00  --large_theory_mode                     true
% 3.26/1.00  --prolific_symb_bound                   200
% 3.26/1.00  --lt_threshold                          2000
% 3.26/1.00  --clause_weak_htbl                      true
% 3.26/1.00  --gc_record_bc_elim                     false
% 3.26/1.00  
% 3.26/1.00  ------ Preprocessing Options
% 3.26/1.00  
% 3.26/1.00  --preprocessing_flag                    true
% 3.26/1.00  --time_out_prep_mult                    0.1
% 3.26/1.00  --splitting_mode                        input
% 3.26/1.00  --splitting_grd                         true
% 3.26/1.00  --splitting_cvd                         false
% 3.26/1.00  --splitting_cvd_svl                     false
% 3.26/1.00  --splitting_nvd                         32
% 3.26/1.00  --sub_typing                            true
% 3.26/1.00  --prep_gs_sim                           true
% 3.26/1.00  --prep_unflatten                        true
% 3.26/1.00  --prep_res_sim                          true
% 3.26/1.00  --prep_upred                            true
% 3.26/1.00  --prep_sem_filter                       exhaustive
% 3.26/1.00  --prep_sem_filter_out                   false
% 3.26/1.00  --pred_elim                             true
% 3.26/1.00  --res_sim_input                         true
% 3.26/1.00  --eq_ax_congr_red                       true
% 3.26/1.00  --pure_diseq_elim                       true
% 3.26/1.00  --brand_transform                       false
% 3.26/1.00  --non_eq_to_eq                          false
% 3.26/1.00  --prep_def_merge                        true
% 3.26/1.00  --prep_def_merge_prop_impl              false
% 3.26/1.00  --prep_def_merge_mbd                    true
% 3.26/1.00  --prep_def_merge_tr_red                 false
% 3.26/1.00  --prep_def_merge_tr_cl                  false
% 3.26/1.00  --smt_preprocessing                     true
% 3.26/1.00  --smt_ac_axioms                         fast
% 3.26/1.00  --preprocessed_out                      false
% 3.26/1.00  --preprocessed_stats                    false
% 3.26/1.00  
% 3.26/1.00  ------ Abstraction refinement Options
% 3.26/1.00  
% 3.26/1.00  --abstr_ref                             []
% 3.26/1.00  --abstr_ref_prep                        false
% 3.26/1.00  --abstr_ref_until_sat                   false
% 3.26/1.00  --abstr_ref_sig_restrict                funpre
% 3.26/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/1.00  --abstr_ref_under                       []
% 3.26/1.00  
% 3.26/1.00  ------ SAT Options
% 3.26/1.00  
% 3.26/1.00  --sat_mode                              false
% 3.26/1.00  --sat_fm_restart_options                ""
% 3.26/1.00  --sat_gr_def                            false
% 3.26/1.00  --sat_epr_types                         true
% 3.26/1.00  --sat_non_cyclic_types                  false
% 3.26/1.00  --sat_finite_models                     false
% 3.26/1.00  --sat_fm_lemmas                         false
% 3.26/1.00  --sat_fm_prep                           false
% 3.26/1.00  --sat_fm_uc_incr                        true
% 3.26/1.00  --sat_out_model                         small
% 3.26/1.00  --sat_out_clauses                       false
% 3.26/1.00  
% 3.26/1.00  ------ QBF Options
% 3.26/1.00  
% 3.26/1.00  --qbf_mode                              false
% 3.26/1.00  --qbf_elim_univ                         false
% 3.26/1.00  --qbf_dom_inst                          none
% 3.26/1.00  --qbf_dom_pre_inst                      false
% 3.26/1.00  --qbf_sk_in                             false
% 3.26/1.00  --qbf_pred_elim                         true
% 3.26/1.00  --qbf_split                             512
% 3.26/1.00  
% 3.26/1.00  ------ BMC1 Options
% 3.26/1.00  
% 3.26/1.00  --bmc1_incremental                      false
% 3.26/1.00  --bmc1_axioms                           reachable_all
% 3.26/1.00  --bmc1_min_bound                        0
% 3.26/1.00  --bmc1_max_bound                        -1
% 3.26/1.00  --bmc1_max_bound_default                -1
% 3.26/1.00  --bmc1_symbol_reachability              true
% 3.26/1.00  --bmc1_property_lemmas                  false
% 3.26/1.00  --bmc1_k_induction                      false
% 3.26/1.00  --bmc1_non_equiv_states                 false
% 3.26/1.00  --bmc1_deadlock                         false
% 3.26/1.00  --bmc1_ucm                              false
% 3.26/1.00  --bmc1_add_unsat_core                   none
% 3.26/1.00  --bmc1_unsat_core_children              false
% 3.26/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/1.00  --bmc1_out_stat                         full
% 3.26/1.00  --bmc1_ground_init                      false
% 3.26/1.00  --bmc1_pre_inst_next_state              false
% 3.26/1.00  --bmc1_pre_inst_state                   false
% 3.26/1.00  --bmc1_pre_inst_reach_state             false
% 3.26/1.00  --bmc1_out_unsat_core                   false
% 3.26/1.00  --bmc1_aig_witness_out                  false
% 3.26/1.00  --bmc1_verbose                          false
% 3.26/1.00  --bmc1_dump_clauses_tptp                false
% 3.26/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.26/1.00  --bmc1_dump_file                        -
% 3.26/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.26/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.26/1.00  --bmc1_ucm_extend_mode                  1
% 3.26/1.00  --bmc1_ucm_init_mode                    2
% 3.26/1.00  --bmc1_ucm_cone_mode                    none
% 3.26/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.26/1.00  --bmc1_ucm_relax_model                  4
% 3.26/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.26/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/1.00  --bmc1_ucm_layered_model                none
% 3.26/1.00  --bmc1_ucm_max_lemma_size               10
% 3.26/1.00  
% 3.26/1.00  ------ AIG Options
% 3.26/1.00  
% 3.26/1.00  --aig_mode                              false
% 3.26/1.00  
% 3.26/1.00  ------ Instantiation Options
% 3.26/1.00  
% 3.26/1.00  --instantiation_flag                    true
% 3.26/1.00  --inst_sos_flag                         false
% 3.26/1.00  --inst_sos_phase                        true
% 3.26/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/1.00  --inst_lit_sel_side                     num_symb
% 3.26/1.00  --inst_solver_per_active                1400
% 3.26/1.00  --inst_solver_calls_frac                1.
% 3.26/1.00  --inst_passive_queue_type               priority_queues
% 3.26/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/1.00  --inst_passive_queues_freq              [25;2]
% 3.26/1.00  --inst_dismatching                      true
% 3.26/1.00  --inst_eager_unprocessed_to_passive     true
% 3.26/1.00  --inst_prop_sim_given                   true
% 3.26/1.00  --inst_prop_sim_new                     false
% 3.26/1.00  --inst_subs_new                         false
% 3.26/1.00  --inst_eq_res_simp                      false
% 3.26/1.00  --inst_subs_given                       false
% 3.26/1.00  --inst_orphan_elimination               true
% 3.26/1.00  --inst_learning_loop_flag               true
% 3.26/1.00  --inst_learning_start                   3000
% 3.26/1.00  --inst_learning_factor                  2
% 3.26/1.00  --inst_start_prop_sim_after_learn       3
% 3.26/1.00  --inst_sel_renew                        solver
% 3.26/1.00  --inst_lit_activity_flag                true
% 3.26/1.00  --inst_restr_to_given                   false
% 3.26/1.00  --inst_activity_threshold               500
% 3.26/1.00  --inst_out_proof                        true
% 3.26/1.00  
% 3.26/1.00  ------ Resolution Options
% 3.26/1.00  
% 3.26/1.00  --resolution_flag                       true
% 3.26/1.00  --res_lit_sel                           adaptive
% 3.26/1.00  --res_lit_sel_side                      none
% 3.26/1.00  --res_ordering                          kbo
% 3.26/1.00  --res_to_prop_solver                    active
% 3.26/1.00  --res_prop_simpl_new                    false
% 3.26/1.00  --res_prop_simpl_given                  true
% 3.26/1.00  --res_passive_queue_type                priority_queues
% 3.26/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/1.00  --res_passive_queues_freq               [15;5]
% 3.26/1.00  --res_forward_subs                      full
% 3.26/1.00  --res_backward_subs                     full
% 3.26/1.00  --res_forward_subs_resolution           true
% 3.26/1.00  --res_backward_subs_resolution          true
% 3.26/1.00  --res_orphan_elimination                true
% 3.26/1.00  --res_time_limit                        2.
% 3.26/1.00  --res_out_proof                         true
% 3.26/1.00  
% 3.26/1.00  ------ Superposition Options
% 3.26/1.00  
% 3.26/1.00  --superposition_flag                    true
% 3.26/1.00  --sup_passive_queue_type                priority_queues
% 3.26/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.26/1.00  --demod_completeness_check              fast
% 3.26/1.00  --demod_use_ground                      true
% 3.26/1.00  --sup_to_prop_solver                    passive
% 3.26/1.00  --sup_prop_simpl_new                    true
% 3.26/1.00  --sup_prop_simpl_given                  true
% 3.26/1.00  --sup_fun_splitting                     false
% 3.26/1.00  --sup_smt_interval                      50000
% 3.26/1.00  
% 3.26/1.00  ------ Superposition Simplification Setup
% 3.26/1.00  
% 3.26/1.00  --sup_indices_passive                   []
% 3.26/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/1.00  --sup_full_bw                           [BwDemod]
% 3.26/1.00  --sup_immed_triv                        [TrivRules]
% 3.26/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/1.00  --sup_immed_bw_main                     []
% 3.26/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/1.00  
% 3.26/1.00  ------ Combination Options
% 3.26/1.00  
% 3.26/1.00  --comb_res_mult                         3
% 3.26/1.00  --comb_sup_mult                         2
% 3.26/1.00  --comb_inst_mult                        10
% 3.26/1.00  
% 3.26/1.00  ------ Debug Options
% 3.26/1.00  
% 3.26/1.00  --dbg_backtrace                         false
% 3.26/1.00  --dbg_dump_prop_clauses                 false
% 3.26/1.00  --dbg_dump_prop_clauses_file            -
% 3.26/1.00  --dbg_out_stat                          false
% 3.26/1.00  ------ Parsing...
% 3.26/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.26/1.00  
% 3.26/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.26/1.00  
% 3.26/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.26/1.00  
% 3.26/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.26/1.00  ------ Proving...
% 3.26/1.00  ------ Problem Properties 
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  clauses                                 57
% 3.26/1.00  conjectures                             4
% 3.26/1.00  EPR                                     7
% 3.26/1.00  Horn                                    41
% 3.26/1.00  unary                                   18
% 3.26/1.00  binary                                  17
% 3.26/1.00  lits                                    128
% 3.26/1.00  lits eq                                 36
% 3.26/1.00  fd_pure                                 0
% 3.26/1.00  fd_pseudo                               0
% 3.26/1.00  fd_cond                                 5
% 3.26/1.00  fd_pseudo_cond                          2
% 3.26/1.00  AC symbols                              0
% 3.26/1.00  
% 3.26/1.00  ------ Schedule dynamic 5 is on 
% 3.26/1.00  
% 3.26/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  ------ 
% 3.26/1.00  Current options:
% 3.26/1.00  ------ 
% 3.26/1.00  
% 3.26/1.00  ------ Input Options
% 3.26/1.00  
% 3.26/1.00  --out_options                           all
% 3.26/1.00  --tptp_safe_out                         true
% 3.26/1.00  --problem_path                          ""
% 3.26/1.00  --include_path                          ""
% 3.26/1.00  --clausifier                            res/vclausify_rel
% 3.26/1.00  --clausifier_options                    --mode clausify
% 3.26/1.00  --stdin                                 false
% 3.26/1.00  --stats_out                             all
% 3.26/1.00  
% 3.26/1.00  ------ General Options
% 3.26/1.00  
% 3.26/1.00  --fof                                   false
% 3.26/1.00  --time_out_real                         305.
% 3.26/1.00  --time_out_virtual                      -1.
% 3.26/1.00  --symbol_type_check                     false
% 3.26/1.00  --clausify_out                          false
% 3.26/1.00  --sig_cnt_out                           false
% 3.26/1.00  --trig_cnt_out                          false
% 3.26/1.00  --trig_cnt_out_tolerance                1.
% 3.26/1.00  --trig_cnt_out_sk_spl                   false
% 3.26/1.00  --abstr_cl_out                          false
% 3.26/1.00  
% 3.26/1.00  ------ Global Options
% 3.26/1.00  
% 3.26/1.00  --schedule                              default
% 3.26/1.00  --add_important_lit                     false
% 3.26/1.00  --prop_solver_per_cl                    1000
% 3.26/1.00  --min_unsat_core                        false
% 3.26/1.00  --soft_assumptions                      false
% 3.26/1.00  --soft_lemma_size                       3
% 3.26/1.00  --prop_impl_unit_size                   0
% 3.26/1.00  --prop_impl_unit                        []
% 3.26/1.00  --share_sel_clauses                     true
% 3.26/1.00  --reset_solvers                         false
% 3.26/1.00  --bc_imp_inh                            [conj_cone]
% 3.26/1.00  --conj_cone_tolerance                   3.
% 3.26/1.00  --extra_neg_conj                        none
% 3.26/1.00  --large_theory_mode                     true
% 3.26/1.00  --prolific_symb_bound                   200
% 3.26/1.00  --lt_threshold                          2000
% 3.26/1.00  --clause_weak_htbl                      true
% 3.26/1.00  --gc_record_bc_elim                     false
% 3.26/1.00  
% 3.26/1.00  ------ Preprocessing Options
% 3.26/1.00  
% 3.26/1.00  --preprocessing_flag                    true
% 3.26/1.00  --time_out_prep_mult                    0.1
% 3.26/1.00  --splitting_mode                        input
% 3.26/1.00  --splitting_grd                         true
% 3.26/1.00  --splitting_cvd                         false
% 3.26/1.00  --splitting_cvd_svl                     false
% 3.26/1.00  --splitting_nvd                         32
% 3.26/1.00  --sub_typing                            true
% 3.26/1.00  --prep_gs_sim                           true
% 3.26/1.00  --prep_unflatten                        true
% 3.26/1.00  --prep_res_sim                          true
% 3.26/1.00  --prep_upred                            true
% 3.26/1.00  --prep_sem_filter                       exhaustive
% 3.26/1.00  --prep_sem_filter_out                   false
% 3.26/1.00  --pred_elim                             true
% 3.26/1.00  --res_sim_input                         true
% 3.26/1.00  --eq_ax_congr_red                       true
% 3.26/1.00  --pure_diseq_elim                       true
% 3.26/1.00  --brand_transform                       false
% 3.26/1.00  --non_eq_to_eq                          false
% 3.26/1.00  --prep_def_merge                        true
% 3.26/1.00  --prep_def_merge_prop_impl              false
% 3.26/1.00  --prep_def_merge_mbd                    true
% 3.26/1.00  --prep_def_merge_tr_red                 false
% 3.26/1.00  --prep_def_merge_tr_cl                  false
% 3.26/1.00  --smt_preprocessing                     true
% 3.26/1.00  --smt_ac_axioms                         fast
% 3.26/1.00  --preprocessed_out                      false
% 3.26/1.00  --preprocessed_stats                    false
% 3.26/1.00  
% 3.26/1.00  ------ Abstraction refinement Options
% 3.26/1.00  
% 3.26/1.00  --abstr_ref                             []
% 3.26/1.00  --abstr_ref_prep                        false
% 3.26/1.00  --abstr_ref_until_sat                   false
% 3.26/1.00  --abstr_ref_sig_restrict                funpre
% 3.26/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/1.00  --abstr_ref_under                       []
% 3.26/1.00  
% 3.26/1.00  ------ SAT Options
% 3.26/1.00  
% 3.26/1.00  --sat_mode                              false
% 3.26/1.00  --sat_fm_restart_options                ""
% 3.26/1.00  --sat_gr_def                            false
% 3.26/1.00  --sat_epr_types                         true
% 3.26/1.00  --sat_non_cyclic_types                  false
% 3.26/1.00  --sat_finite_models                     false
% 3.26/1.00  --sat_fm_lemmas                         false
% 3.26/1.00  --sat_fm_prep                           false
% 3.26/1.00  --sat_fm_uc_incr                        true
% 3.26/1.00  --sat_out_model                         small
% 3.26/1.00  --sat_out_clauses                       false
% 3.26/1.00  
% 3.26/1.00  ------ QBF Options
% 3.26/1.00  
% 3.26/1.00  --qbf_mode                              false
% 3.26/1.00  --qbf_elim_univ                         false
% 3.26/1.00  --qbf_dom_inst                          none
% 3.26/1.00  --qbf_dom_pre_inst                      false
% 3.26/1.00  --qbf_sk_in                             false
% 3.26/1.00  --qbf_pred_elim                         true
% 3.26/1.00  --qbf_split                             512
% 3.26/1.00  
% 3.26/1.00  ------ BMC1 Options
% 3.26/1.00  
% 3.26/1.00  --bmc1_incremental                      false
% 3.26/1.00  --bmc1_axioms                           reachable_all
% 3.26/1.00  --bmc1_min_bound                        0
% 3.26/1.00  --bmc1_max_bound                        -1
% 3.26/1.00  --bmc1_max_bound_default                -1
% 3.26/1.00  --bmc1_symbol_reachability              true
% 3.26/1.00  --bmc1_property_lemmas                  false
% 3.26/1.00  --bmc1_k_induction                      false
% 3.26/1.00  --bmc1_non_equiv_states                 false
% 3.26/1.00  --bmc1_deadlock                         false
% 3.26/1.00  --bmc1_ucm                              false
% 3.26/1.00  --bmc1_add_unsat_core                   none
% 3.26/1.00  --bmc1_unsat_core_children              false
% 3.26/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/1.00  --bmc1_out_stat                         full
% 3.26/1.00  --bmc1_ground_init                      false
% 3.26/1.00  --bmc1_pre_inst_next_state              false
% 3.26/1.00  --bmc1_pre_inst_state                   false
% 3.26/1.00  --bmc1_pre_inst_reach_state             false
% 3.26/1.00  --bmc1_out_unsat_core                   false
% 3.26/1.00  --bmc1_aig_witness_out                  false
% 3.26/1.00  --bmc1_verbose                          false
% 3.26/1.00  --bmc1_dump_clauses_tptp                false
% 3.26/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.26/1.00  --bmc1_dump_file                        -
% 3.26/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.26/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.26/1.00  --bmc1_ucm_extend_mode                  1
% 3.26/1.00  --bmc1_ucm_init_mode                    2
% 3.26/1.00  --bmc1_ucm_cone_mode                    none
% 3.26/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.26/1.00  --bmc1_ucm_relax_model                  4
% 3.26/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.26/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/1.00  --bmc1_ucm_layered_model                none
% 3.26/1.00  --bmc1_ucm_max_lemma_size               10
% 3.26/1.00  
% 3.26/1.00  ------ AIG Options
% 3.26/1.00  
% 3.26/1.00  --aig_mode                              false
% 3.26/1.00  
% 3.26/1.00  ------ Instantiation Options
% 3.26/1.00  
% 3.26/1.00  --instantiation_flag                    true
% 3.26/1.00  --inst_sos_flag                         false
% 3.26/1.00  --inst_sos_phase                        true
% 3.26/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/1.00  --inst_lit_sel_side                     none
% 3.26/1.00  --inst_solver_per_active                1400
% 3.26/1.00  --inst_solver_calls_frac                1.
% 3.26/1.00  --inst_passive_queue_type               priority_queues
% 3.26/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/1.00  --inst_passive_queues_freq              [25;2]
% 3.26/1.00  --inst_dismatching                      true
% 3.26/1.00  --inst_eager_unprocessed_to_passive     true
% 3.26/1.00  --inst_prop_sim_given                   true
% 3.26/1.00  --inst_prop_sim_new                     false
% 3.26/1.00  --inst_subs_new                         false
% 3.26/1.00  --inst_eq_res_simp                      false
% 3.26/1.00  --inst_subs_given                       false
% 3.26/1.00  --inst_orphan_elimination               true
% 3.26/1.00  --inst_learning_loop_flag               true
% 3.26/1.00  --inst_learning_start                   3000
% 3.26/1.00  --inst_learning_factor                  2
% 3.26/1.00  --inst_start_prop_sim_after_learn       3
% 3.26/1.00  --inst_sel_renew                        solver
% 3.26/1.00  --inst_lit_activity_flag                true
% 3.26/1.00  --inst_restr_to_given                   false
% 3.26/1.00  --inst_activity_threshold               500
% 3.26/1.00  --inst_out_proof                        true
% 3.26/1.00  
% 3.26/1.00  ------ Resolution Options
% 3.26/1.00  
% 3.26/1.00  --resolution_flag                       false
% 3.26/1.00  --res_lit_sel                           adaptive
% 3.26/1.00  --res_lit_sel_side                      none
% 3.26/1.00  --res_ordering                          kbo
% 3.26/1.00  --res_to_prop_solver                    active
% 3.26/1.00  --res_prop_simpl_new                    false
% 3.26/1.00  --res_prop_simpl_given                  true
% 3.26/1.00  --res_passive_queue_type                priority_queues
% 3.26/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/1.00  --res_passive_queues_freq               [15;5]
% 3.26/1.00  --res_forward_subs                      full
% 3.26/1.00  --res_backward_subs                     full
% 3.26/1.00  --res_forward_subs_resolution           true
% 3.26/1.00  --res_backward_subs_resolution          true
% 3.26/1.00  --res_orphan_elimination                true
% 3.26/1.00  --res_time_limit                        2.
% 3.26/1.00  --res_out_proof                         true
% 3.26/1.00  
% 3.26/1.00  ------ Superposition Options
% 3.26/1.00  
% 3.26/1.00  --superposition_flag                    true
% 3.26/1.00  --sup_passive_queue_type                priority_queues
% 3.26/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.26/1.00  --demod_completeness_check              fast
% 3.26/1.00  --demod_use_ground                      true
% 3.26/1.00  --sup_to_prop_solver                    passive
% 3.26/1.00  --sup_prop_simpl_new                    true
% 3.26/1.00  --sup_prop_simpl_given                  true
% 3.26/1.00  --sup_fun_splitting                     false
% 3.26/1.00  --sup_smt_interval                      50000
% 3.26/1.00  
% 3.26/1.00  ------ Superposition Simplification Setup
% 3.26/1.00  
% 3.26/1.00  --sup_indices_passive                   []
% 3.26/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/1.00  --sup_full_bw                           [BwDemod]
% 3.26/1.00  --sup_immed_triv                        [TrivRules]
% 3.26/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/1.00  --sup_immed_bw_main                     []
% 3.26/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/1.00  
% 3.26/1.00  ------ Combination Options
% 3.26/1.00  
% 3.26/1.00  --comb_res_mult                         3
% 3.26/1.00  --comb_sup_mult                         2
% 3.26/1.00  --comb_inst_mult                        10
% 3.26/1.00  
% 3.26/1.00  ------ Debug Options
% 3.26/1.00  
% 3.26/1.00  --dbg_backtrace                         false
% 3.26/1.00  --dbg_dump_prop_clauses                 false
% 3.26/1.00  --dbg_dump_prop_clauses_file            -
% 3.26/1.00  --dbg_out_stat                          false
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  ------ Proving...
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  % SZS status Theorem for theBenchmark.p
% 3.26/1.00  
% 3.26/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.26/1.00  
% 3.26/1.00  fof(f17,axiom,(
% 3.26/1.00    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f38,plain,(
% 3.26/1.00    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 3.26/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.26/1.00  
% 3.26/1.00  fof(f39,plain,(
% 3.26/1.00    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 3.26/1.00    inference(definition_folding,[],[f17,f38])).
% 3.26/1.00  
% 3.26/1.00  fof(f64,plain,(
% 3.26/1.00    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 3.26/1.00    inference(nnf_transformation,[],[f39])).
% 3.26/1.00  
% 3.26/1.00  fof(f119,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 3.26/1.00    inference(cnf_transformation,[],[f64])).
% 3.26/1.00  
% 3.26/1.00  fof(f150,plain,(
% 3.26/1.00    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 3.26/1.00    inference(equality_resolution,[],[f119])).
% 3.26/1.00  
% 3.26/1.00  fof(f3,axiom,(
% 3.26/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f48,plain,(
% 3.26/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.26/1.00    inference(nnf_transformation,[],[f3])).
% 3.26/1.00  
% 3.26/1.00  fof(f49,plain,(
% 3.26/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.26/1.00    inference(flattening,[],[f48])).
% 3.26/1.00  
% 3.26/1.00  fof(f74,plain,(
% 3.26/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.26/1.00    inference(cnf_transformation,[],[f49])).
% 3.26/1.00  
% 3.26/1.00  fof(f135,plain,(
% 3.26/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.26/1.00    inference(equality_resolution,[],[f74])).
% 3.26/1.00  
% 3.26/1.00  fof(f16,axiom,(
% 3.26/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f32,plain,(
% 3.26/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/1.00    inference(ennf_transformation,[],[f16])).
% 3.26/1.00  
% 3.26/1.00  fof(f33,plain,(
% 3.26/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/1.00    inference(flattening,[],[f32])).
% 3.26/1.00  
% 3.26/1.00  fof(f57,plain,(
% 3.26/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/1.00    inference(nnf_transformation,[],[f33])).
% 3.26/1.00  
% 3.26/1.00  fof(f101,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/1.00    inference(cnf_transformation,[],[f57])).
% 3.26/1.00  
% 3.26/1.00  fof(f20,conjecture,(
% 3.26/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f21,negated_conjecture,(
% 3.26/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 3.26/1.00    inference(negated_conjecture,[],[f20])).
% 3.26/1.00  
% 3.26/1.00  fof(f36,plain,(
% 3.26/1.00    ? [X0,X1,X2] : ((~r2_hidden(X2,k1_funct_2(X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.26/1.00    inference(ennf_transformation,[],[f21])).
% 3.26/1.00  
% 3.26/1.00  fof(f37,plain,(
% 3.26/1.00    ? [X0,X1,X2] : (~r2_hidden(X2,k1_funct_2(X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.26/1.00    inference(flattening,[],[f36])).
% 3.26/1.00  
% 3.26/1.00  fof(f67,plain,(
% 3.26/1.00    ? [X0,X1,X2] : (~r2_hidden(X2,k1_funct_2(X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (~r2_hidden(sK10,k1_funct_2(sK8,sK9)) & (k1_xboole_0 = sK8 | k1_xboole_0 != sK9) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) & v1_funct_2(sK10,sK8,sK9) & v1_funct_1(sK10))),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f68,plain,(
% 3.26/1.00    ~r2_hidden(sK10,k1_funct_2(sK8,sK9)) & (k1_xboole_0 = sK8 | k1_xboole_0 != sK9) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) & v1_funct_2(sK10,sK8,sK9) & v1_funct_1(sK10)),
% 3.26/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f37,f67])).
% 3.26/1.00  
% 3.26/1.00  fof(f130,plain,(
% 3.26/1.00    v1_funct_2(sK10,sK8,sK9)),
% 3.26/1.00    inference(cnf_transformation,[],[f68])).
% 3.26/1.00  
% 3.26/1.00  fof(f131,plain,(
% 3.26/1.00    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))),
% 3.26/1.00    inference(cnf_transformation,[],[f68])).
% 3.26/1.00  
% 3.26/1.00  fof(f14,axiom,(
% 3.26/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f30,plain,(
% 3.26/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/1.00    inference(ennf_transformation,[],[f14])).
% 3.26/1.00  
% 3.26/1.00  fof(f99,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/1.00    inference(cnf_transformation,[],[f30])).
% 3.26/1.00  
% 3.26/1.00  fof(f58,plain,(
% 3.26/1.00    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 3.26/1.00    inference(nnf_transformation,[],[f38])).
% 3.26/1.00  
% 3.26/1.00  fof(f59,plain,(
% 3.26/1.00    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 3.26/1.00    inference(rectify,[],[f58])).
% 3.26/1.00  
% 3.26/1.00  fof(f62,plain,(
% 3.26/1.00    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X0) & k1_relat_1(sK6(X0,X1,X6)) = X1 & sK6(X0,X1,X6) = X6 & v1_funct_1(sK6(X0,X1,X6)) & v1_relat_1(sK6(X0,X1,X6))))),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f61,plain,(
% 3.26/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X0) & k1_relat_1(sK5(X0,X1,X2)) = X1 & sK5(X0,X1,X2) = X3 & v1_funct_1(sK5(X0,X1,X2)) & v1_relat_1(sK5(X0,X1,X2))))) )),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f60,plain,(
% 3.26/1.00    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK4(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK4(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f63,plain,(
% 3.26/1.00    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK4(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X0) & k1_relat_1(sK5(X0,X1,X2)) = X1 & sK4(X0,X1,X2) = sK5(X0,X1,X2) & v1_funct_1(sK5(X0,X1,X2)) & v1_relat_1(sK5(X0,X1,X2))) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X0) & k1_relat_1(sK6(X0,X1,X6)) = X1 & sK6(X0,X1,X6) = X6 & v1_funct_1(sK6(X0,X1,X6)) & v1_relat_1(sK6(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 3.26/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f59,f62,f61,f60])).
% 3.26/1.00  
% 3.26/1.00  fof(f112,plain,(
% 3.26/1.00    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7) | ~sP0(X0,X1,X2)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f63])).
% 3.26/1.00  
% 3.26/1.00  fof(f148,plain,(
% 3.26/1.00    ( ! [X6,X2,X0,X7] : (r2_hidden(X6,X2) | ~r1_tarski(k2_relat_1(X7),X0) | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7) | ~sP0(X0,k1_relat_1(X7),X2)) )),
% 3.26/1.00    inference(equality_resolution,[],[f112])).
% 3.26/1.00  
% 3.26/1.00  fof(f149,plain,(
% 3.26/1.00    ( ! [X2,X0,X7] : (r2_hidden(X7,X2) | ~r1_tarski(k2_relat_1(X7),X0) | ~v1_funct_1(X7) | ~v1_relat_1(X7) | ~sP0(X0,k1_relat_1(X7),X2)) )),
% 3.26/1.00    inference(equality_resolution,[],[f148])).
% 3.26/1.00  
% 3.26/1.00  fof(f129,plain,(
% 3.26/1.00    v1_funct_1(sK10)),
% 3.26/1.00    inference(cnf_transformation,[],[f68])).
% 3.26/1.00  
% 3.26/1.00  fof(f11,axiom,(
% 3.26/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f27,plain,(
% 3.26/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/1.00    inference(ennf_transformation,[],[f11])).
% 3.26/1.00  
% 3.26/1.00  fof(f96,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/1.00    inference(cnf_transformation,[],[f27])).
% 3.26/1.00  
% 3.26/1.00  fof(f133,plain,(
% 3.26/1.00    ~r2_hidden(sK10,k1_funct_2(sK8,sK9))),
% 3.26/1.00    inference(cnf_transformation,[],[f68])).
% 3.26/1.00  
% 3.26/1.00  fof(f15,axiom,(
% 3.26/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f31,plain,(
% 3.26/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/1.00    inference(ennf_transformation,[],[f15])).
% 3.26/1.00  
% 3.26/1.00  fof(f100,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/1.00    inference(cnf_transformation,[],[f31])).
% 3.26/1.00  
% 3.26/1.00  fof(f13,axiom,(
% 3.26/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f29,plain,(
% 3.26/1.00    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/1.00    inference(ennf_transformation,[],[f13])).
% 3.26/1.00  
% 3.26/1.00  fof(f98,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/1.00    inference(cnf_transformation,[],[f29])).
% 3.26/1.00  
% 3.26/1.00  fof(f6,axiom,(
% 3.26/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f52,plain,(
% 3.26/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.26/1.00    inference(nnf_transformation,[],[f6])).
% 3.26/1.00  
% 3.26/1.00  fof(f81,plain,(
% 3.26/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.26/1.00    inference(cnf_transformation,[],[f52])).
% 3.26/1.00  
% 3.26/1.00  fof(f132,plain,(
% 3.26/1.00    k1_xboole_0 = sK8 | k1_xboole_0 != sK9),
% 3.26/1.00    inference(cnf_transformation,[],[f68])).
% 3.26/1.00  
% 3.26/1.00  fof(f102,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/1.00    inference(cnf_transformation,[],[f57])).
% 3.26/1.00  
% 3.26/1.00  fof(f146,plain,(
% 3.26/1.00    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.26/1.00    inference(equality_resolution,[],[f102])).
% 3.26/1.00  
% 3.26/1.00  fof(f5,axiom,(
% 3.26/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f50,plain,(
% 3.26/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.26/1.00    inference(nnf_transformation,[],[f5])).
% 3.26/1.00  
% 3.26/1.00  fof(f51,plain,(
% 3.26/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.26/1.00    inference(flattening,[],[f50])).
% 3.26/1.00  
% 3.26/1.00  fof(f79,plain,(
% 3.26/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.26/1.00    inference(cnf_transformation,[],[f51])).
% 3.26/1.00  
% 3.26/1.00  fof(f137,plain,(
% 3.26/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.26/1.00    inference(equality_resolution,[],[f79])).
% 3.26/1.00  
% 3.26/1.00  fof(f2,axiom,(
% 3.26/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f22,plain,(
% 3.26/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.26/1.00    inference(ennf_transformation,[],[f2])).
% 3.26/1.00  
% 3.26/1.00  fof(f44,plain,(
% 3.26/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.26/1.00    inference(nnf_transformation,[],[f22])).
% 3.26/1.00  
% 3.26/1.00  fof(f45,plain,(
% 3.26/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.26/1.00    inference(rectify,[],[f44])).
% 3.26/1.00  
% 3.26/1.00  fof(f46,plain,(
% 3.26/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f47,plain,(
% 3.26/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.26/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).
% 3.26/1.00  
% 3.26/1.00  fof(f72,plain,(
% 3.26/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f47])).
% 3.26/1.00  
% 3.26/1.00  fof(f1,axiom,(
% 3.26/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f40,plain,(
% 3.26/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.26/1.00    inference(nnf_transformation,[],[f1])).
% 3.26/1.00  
% 3.26/1.00  fof(f41,plain,(
% 3.26/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.26/1.00    inference(rectify,[],[f40])).
% 3.26/1.00  
% 3.26/1.00  fof(f42,plain,(
% 3.26/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f43,plain,(
% 3.26/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.26/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 3.26/1.00  
% 3.26/1.00  fof(f69,plain,(
% 3.26/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f43])).
% 3.26/1.00  
% 3.26/1.00  fof(f76,plain,(
% 3.26/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f49])).
% 3.26/1.00  
% 3.26/1.00  fof(f4,axiom,(
% 3.26/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f77,plain,(
% 3.26/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f4])).
% 3.26/1.00  
% 3.26/1.00  fof(f19,axiom,(
% 3.26/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f34,plain,(
% 3.26/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.26/1.00    inference(ennf_transformation,[],[f19])).
% 3.26/1.00  
% 3.26/1.00  fof(f35,plain,(
% 3.26/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.26/1.00    inference(flattening,[],[f34])).
% 3.26/1.00  
% 3.26/1.00  fof(f127,plain,(
% 3.26/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f35])).
% 3.26/1.00  
% 3.26/1.00  fof(f128,plain,(
% 3.26/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f35])).
% 3.26/1.00  
% 3.26/1.00  cnf(c_51,plain,
% 3.26/1.00      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 3.26/1.00      inference(cnf_transformation,[],[f150]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7117,plain,
% 3.26/1.00      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7,plain,
% 3.26/1.00      ( r1_tarski(X0,X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f135]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7146,plain,
% 3.26/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_37,plain,
% 3.26/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.26/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.26/1.00      | k1_xboole_0 = X2 ),
% 3.26/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_63,negated_conjecture,
% 3.26/1.00      ( v1_funct_2(sK10,sK8,sK9) ),
% 3.26/1.00      inference(cnf_transformation,[],[f130]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_920,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.26/1.00      | sK9 != X2
% 3.26/1.00      | sK8 != X1
% 3.26/1.00      | sK10 != X0
% 3.26/1.00      | k1_xboole_0 = X2 ),
% 3.26/1.00      inference(resolution_lifted,[status(thm)],[c_37,c_63]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_921,plain,
% 3.26/1.00      ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
% 3.26/1.00      | k1_relset_1(sK8,sK9,sK10) = sK8
% 3.26/1.00      | k1_xboole_0 = sK9 ),
% 3.26/1.00      inference(unflattening,[status(thm)],[c_920]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_62,negated_conjecture,
% 3.26/1.00      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
% 3.26/1.00      inference(cnf_transformation,[],[f131]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_923,plain,
% 3.26/1.00      ( k1_relset_1(sK8,sK9,sK10) = sK8 | k1_xboole_0 = sK9 ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_921,c_62]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7111,plain,
% 3.26/1.00      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_30,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7132,plain,
% 3.26/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.26/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_10005,plain,
% 3.26/1.00      ( k1_relset_1(sK8,sK9,sK10) = k1_relat_1(sK10) ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_7111,c_7132]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_10067,plain,
% 3.26/1.00      ( k1_relat_1(sK10) = sK8 | sK9 = k1_xboole_0 ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_923,c_10005]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_44,plain,
% 3.26/1.00      ( ~ sP0(X0,k1_relat_1(X1),X2)
% 3.26/1.00      | ~ r1_tarski(k2_relat_1(X1),X0)
% 3.26/1.00      | r2_hidden(X1,X2)
% 3.26/1.00      | ~ v1_funct_1(X1)
% 3.26/1.00      | ~ v1_relat_1(X1) ),
% 3.26/1.00      inference(cnf_transformation,[],[f149]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7124,plain,
% 3.26/1.00      ( sP0(X0,k1_relat_1(X1),X2) != iProver_top
% 3.26/1.00      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 3.26/1.00      | r2_hidden(X1,X2) = iProver_top
% 3.26/1.00      | v1_funct_1(X1) != iProver_top
% 3.26/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12072,plain,
% 3.26/1.00      ( sK9 = k1_xboole_0
% 3.26/1.00      | sP0(X0,sK8,X1) != iProver_top
% 3.26/1.00      | r1_tarski(k2_relat_1(sK10),X0) != iProver_top
% 3.26/1.00      | r2_hidden(sK10,X1) = iProver_top
% 3.26/1.00      | v1_funct_1(sK10) != iProver_top
% 3.26/1.00      | v1_relat_1(sK10) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_10067,c_7124]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_64,negated_conjecture,
% 3.26/1.00      ( v1_funct_1(sK10) ),
% 3.26/1.00      inference(cnf_transformation,[],[f129]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_65,plain,
% 3.26/1.00      ( v1_funct_1(sK10) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_67,plain,
% 3.26/1.00      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_27,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/1.00      | v1_relat_1(X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7535,plain,
% 3.26/1.00      ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
% 3.26/1.00      | v1_relat_1(sK10) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_27]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7536,plain,
% 3.26/1.00      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) != iProver_top
% 3.26/1.00      | v1_relat_1(sK10) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_7535]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12528,plain,
% 3.26/1.00      ( sK9 = k1_xboole_0
% 3.26/1.00      | sP0(X0,sK8,X1) != iProver_top
% 3.26/1.00      | r1_tarski(k2_relat_1(sK10),X0) != iProver_top
% 3.26/1.00      | r2_hidden(sK10,X1) = iProver_top ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_12072,c_65,c_67,c_7536]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12539,plain,
% 3.26/1.00      ( sK9 = k1_xboole_0
% 3.26/1.00      | sP0(k2_relat_1(sK10),sK8,X0) != iProver_top
% 3.26/1.00      | r2_hidden(sK10,X0) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_7146,c_12528]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_60,negated_conjecture,
% 3.26/1.00      ( ~ r2_hidden(sK10,k1_funct_2(sK8,sK9)) ),
% 3.26/1.00      inference(cnf_transformation,[],[f133]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_68,plain,
% 3.26/1.00      ( r2_hidden(sK10,k1_funct_2(sK8,sK9)) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_31,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7131,plain,
% 3.26/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.26/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_9815,plain,
% 3.26/1.00      ( k2_relset_1(sK8,sK9,sK10) = k2_relat_1(sK10) ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_7111,c_7131]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_29,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/1.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.26/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7133,plain,
% 3.26/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.26/1.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_10945,plain,
% 3.26/1.00      ( m1_subset_1(k2_relat_1(sK10),k1_zfmisc_1(sK9)) = iProver_top
% 3.26/1.00      | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_9815,c_7133]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_11158,plain,
% 3.26/1.00      ( m1_subset_1(k2_relat_1(sK10),k1_zfmisc_1(sK9)) = iProver_top ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_10945,c_67]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_13,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.26/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7143,plain,
% 3.26/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.26/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_11163,plain,
% 3.26/1.00      ( r1_tarski(k2_relat_1(sK10),sK9) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_11158,c_7143]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12540,plain,
% 3.26/1.00      ( sK9 = k1_xboole_0
% 3.26/1.00      | sP0(sK9,sK8,X0) != iProver_top
% 3.26/1.00      | r2_hidden(sK10,X0) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_11163,c_12528]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12574,plain,
% 3.26/1.00      ( sK9 = k1_xboole_0
% 3.26/1.00      | r2_hidden(sK10,k1_funct_2(sK8,sK9)) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_7117,c_12540]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12756,plain,
% 3.26/1.00      ( sK9 = k1_xboole_0 ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_12539,c_68,c_12574]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12771,plain,
% 3.26/1.00      ( k1_relset_1(sK8,k1_xboole_0,sK10) = k1_relat_1(sK10) ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_12756,c_10005]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_61,negated_conjecture,
% 3.26/1.00      ( k1_xboole_0 != sK9 | k1_xboole_0 = sK8 ),
% 3.26/1.00      inference(cnf_transformation,[],[f132]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12779,plain,
% 3.26/1.00      ( sK8 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_12756,c_61]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12780,plain,
% 3.26/1.00      ( sK8 = k1_xboole_0 ),
% 3.26/1.00      inference(equality_resolution_simp,[status(thm)],[c_12779]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_36,plain,
% 3.26/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.26/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.26/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.26/1.00      inference(cnf_transformation,[],[f146]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_883,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.26/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.26/1.00      | sK9 != X1
% 3.26/1.00      | sK8 != k1_xboole_0
% 3.26/1.00      | sK10 != X0 ),
% 3.26/1.00      inference(resolution_lifted,[status(thm)],[c_36,c_63]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_884,plain,
% 3.26/1.00      ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK9)))
% 3.26/1.00      | k1_relset_1(k1_xboole_0,sK9,sK10) = k1_xboole_0
% 3.26/1.00      | sK8 != k1_xboole_0 ),
% 3.26/1.00      inference(unflattening,[status(thm)],[c_883]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7104,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,sK9,sK10) = k1_xboole_0
% 3.26/1.00      | sK8 != k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK9))) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_884]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_10,plain,
% 3.26/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.26/1.00      inference(cnf_transformation,[],[f137]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7281,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,sK9,sK10) = k1_xboole_0
% 3.26/1.00      | sK8 != k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK10,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_7104,c_10]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12775,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK10) = k1_xboole_0
% 3.26/1.00      | sK8 != k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK10,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_12756,c_7281]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12790,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK10) = k1_xboole_0
% 3.26/1.00      | k1_xboole_0 != k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK10,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.26/1.00      inference(light_normalisation,[status(thm)],[c_12775,c_12780]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12791,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK10) = k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK10,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.26/1.00      inference(equality_resolution_simp,[status(thm)],[c_12790]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12778,plain,
% 3.26/1.00      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,k1_xboole_0))) = iProver_top ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_12756,c_7111]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12783,plain,
% 3.26/1.00      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.26/1.00      inference(light_normalisation,[status(thm)],[c_12778,c_12780]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12785,plain,
% 3.26/1.00      ( m1_subset_1(sK10,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_12783,c_10]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12794,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK10) = k1_xboole_0 ),
% 3.26/1.00      inference(forward_subsumption_resolution,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_12791,c_12785]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12804,plain,
% 3.26/1.00      ( k1_relat_1(sK10) = k1_xboole_0 ),
% 3.26/1.00      inference(light_normalisation,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_12771,c_12780,c_12794]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12951,plain,
% 3.26/1.00      ( sP0(X0,k1_xboole_0,X1) != iProver_top
% 3.26/1.00      | r1_tarski(k2_relat_1(sK10),X0) != iProver_top
% 3.26/1.00      | r2_hidden(sK10,X1) = iProver_top
% 3.26/1.00      | v1_funct_1(sK10) != iProver_top
% 3.26/1.00      | v1_relat_1(sK10) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_12804,c_7124]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_13952,plain,
% 3.26/1.00      ( sP0(X0,k1_xboole_0,X1) != iProver_top
% 3.26/1.00      | r1_tarski(k2_relat_1(sK10),X0) != iProver_top
% 3.26/1.00      | r2_hidden(sK10,X1) = iProver_top ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_12951,c_65,c_67,c_7536]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3,plain,
% 3.26/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7149,plain,
% 3.26/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.26/1.00      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1,plain,
% 3.26/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.26/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7151,plain,
% 3.26/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.26/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_9093,plain,
% 3.26/1.00      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_7149,c_7151]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8640,plain,
% 3.26/1.00      ( r1_tarski(sK10,k2_zfmisc_1(sK8,sK9)) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_7111,c_7143]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_5,plain,
% 3.26/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.26/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7147,plain,
% 3.26/1.00      ( X0 = X1
% 3.26/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.26/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_10865,plain,
% 3.26/1.00      ( k2_zfmisc_1(sK8,sK9) = sK10
% 3.26/1.00      | r1_tarski(k2_zfmisc_1(sK8,sK9),sK10) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_8640,c_7147]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_11155,plain,
% 3.26/1.00      ( k2_zfmisc_1(sK8,sK9) = sK10
% 3.26/1.00      | v1_xboole_0(k2_zfmisc_1(sK8,sK9)) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_9093,c_10865]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12767,plain,
% 3.26/1.00      ( k2_zfmisc_1(sK8,k1_xboole_0) = sK10
% 3.26/1.00      | v1_xboole_0(k2_zfmisc_1(sK8,k1_xboole_0)) != iProver_top ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_12756,c_11155]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12817,plain,
% 3.26/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK10
% 3.26/1.00      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.26/1.00      inference(light_normalisation,[status(thm)],[c_12767,c_12780]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12820,plain,
% 3.26/1.00      ( sK10 = k1_xboole_0 | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_12817,c_10]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8611,plain,
% 3.26/1.00      ( ~ r1_tarski(X0,sK10) | ~ r1_tarski(sK10,X0) | sK10 = X0 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8612,plain,
% 3.26/1.00      ( sK10 = X0
% 3.26/1.00      | r1_tarski(X0,sK10) != iProver_top
% 3.26/1.00      | r1_tarski(sK10,X0) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_8611]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8614,plain,
% 3.26/1.00      ( sK10 = k1_xboole_0
% 3.26/1.00      | r1_tarski(sK10,k1_xboole_0) != iProver_top
% 3.26/1.00      | r1_tarski(k1_xboole_0,sK10) != iProver_top ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_8612]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8,plain,
% 3.26/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_9039,plain,
% 3.26/1.00      ( r1_tarski(k1_xboole_0,sK10) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_9042,plain,
% 3.26/1.00      ( r1_tarski(k1_xboole_0,sK10) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_9039]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_11987,plain,
% 3.26/1.00      ( ~ m1_subset_1(sK10,k1_zfmisc_1(X0)) | r1_tarski(sK10,X0) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_11988,plain,
% 3.26/1.00      ( m1_subset_1(sK10,k1_zfmisc_1(X0)) != iProver_top
% 3.26/1.00      | r1_tarski(sK10,X0) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_11987]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_11990,plain,
% 3.26/1.00      ( m1_subset_1(sK10,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.26/1.00      | r1_tarski(sK10,k1_xboole_0) = iProver_top ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_11988]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_13514,plain,
% 3.26/1.00      ( sK10 = k1_xboole_0 ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_12820,c_8614,c_9042,c_11990,c_12785]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7110,plain,
% 3.26/1.00      ( v1_funct_1(sK10) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_58,plain,
% 3.26/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.26/1.00      | ~ v1_funct_1(X0)
% 3.26/1.00      | ~ v1_relat_1(X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f127]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_896,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/1.00      | ~ v1_funct_1(X3)
% 3.26/1.00      | ~ v1_relat_1(X3)
% 3.26/1.00      | X3 != X0
% 3.26/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.26/1.00      | k2_relat_1(X3) != X2
% 3.26/1.00      | k1_relat_1(X3) != X1
% 3.26/1.00      | k1_xboole_0 = X2 ),
% 3.26/1.00      inference(resolution_lifted,[status(thm)],[c_37,c_58]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_897,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.26/1.00      | ~ v1_funct_1(X0)
% 3.26/1.00      | ~ v1_relat_1(X0)
% 3.26/1.00      | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 3.26/1.00      | k1_xboole_0 = k2_relat_1(X0) ),
% 3.26/1.00      inference(unflattening,[status(thm)],[c_896]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_57,plain,
% 3.26/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.26/1.00      | ~ v1_funct_1(X0)
% 3.26/1.00      | ~ v1_relat_1(X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f128]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_901,plain,
% 3.26/1.00      ( ~ v1_funct_1(X0)
% 3.26/1.00      | ~ v1_relat_1(X0)
% 3.26/1.00      | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 3.26/1.00      | k1_xboole_0 = k2_relat_1(X0) ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_897,c_57]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7103,plain,
% 3.26/1.00      ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 3.26/1.00      | k1_xboole_0 = k2_relat_1(X0)
% 3.26/1.00      | v1_funct_1(X0) != iProver_top
% 3.26/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_901]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7624,plain,
% 3.26/1.00      ( k1_relset_1(k1_relat_1(sK10),k2_relat_1(sK10),sK10) = k1_relat_1(sK10)
% 3.26/1.00      | k2_relat_1(sK10) = k1_xboole_0
% 3.26/1.00      | v1_relat_1(sK10) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_7110,c_7103]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2113,plain,
% 3.26/1.00      ( ~ v1_relat_1(X0)
% 3.26/1.00      | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 3.26/1.00      | k2_relat_1(X0) = k1_xboole_0
% 3.26/1.00      | sK10 != X0 ),
% 3.26/1.00      inference(resolution_lifted,[status(thm)],[c_901,c_64]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2114,plain,
% 3.26/1.00      ( ~ v1_relat_1(sK10)
% 3.26/1.00      | k1_relset_1(k1_relat_1(sK10),k2_relat_1(sK10),sK10) = k1_relat_1(sK10)
% 3.26/1.00      | k2_relat_1(sK10) = k1_xboole_0 ),
% 3.26/1.00      inference(unflattening,[status(thm)],[c_2113]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7657,plain,
% 3.26/1.00      ( k2_relat_1(sK10) = k1_xboole_0
% 3.26/1.00      | k1_relset_1(k1_relat_1(sK10),k2_relat_1(sK10),sK10) = k1_relat_1(sK10) ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_7624,c_62,c_2114,c_7535]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7658,plain,
% 3.26/1.00      ( k1_relset_1(k1_relat_1(sK10),k2_relat_1(sK10),sK10) = k1_relat_1(sK10)
% 3.26/1.00      | k2_relat_1(sK10) = k1_xboole_0 ),
% 3.26/1.00      inference(renaming,[status(thm)],[c_7657]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12949,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK10),sK10) = k1_xboole_0
% 3.26/1.00      | k2_relat_1(sK10) = k1_xboole_0 ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_12804,c_7658]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_9232,plain,
% 3.26/1.00      ( r1_tarski(k1_xboole_0,k2_relat_1(sK10)) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_9235,plain,
% 3.26/1.00      ( r1_tarski(k1_xboole_0,k2_relat_1(sK10)) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_9232]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_11240,plain,
% 3.26/1.00      ( k2_relat_1(sK10) = sK9
% 3.26/1.00      | r1_tarski(sK9,k2_relat_1(sK10)) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_11163,c_7147]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12766,plain,
% 3.26/1.00      ( k2_relat_1(sK10) = k1_xboole_0
% 3.26/1.00      | r1_tarski(k1_xboole_0,k2_relat_1(sK10)) != iProver_top ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_12756,c_11240]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_13630,plain,
% 3.26/1.00      ( k2_relat_1(sK10) = k1_xboole_0 ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_12949,c_9235,c_12766]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_13632,plain,
% 3.26/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.26/1.00      inference(light_normalisation,[status(thm)],[c_13630,c_13514]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_13958,plain,
% 3.26/1.00      ( sP0(X0,k1_xboole_0,X1) != iProver_top
% 3.26/1.00      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 3.26/1.00      | r2_hidden(k1_xboole_0,X1) = iProver_top ),
% 3.26/1.00      inference(light_normalisation,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_13952,c_13514,c_13632]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7145,plain,
% 3.26/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_13962,plain,
% 3.26/1.00      ( sP0(X0,k1_xboole_0,X1) != iProver_top
% 3.26/1.00      | r2_hidden(k1_xboole_0,X1) = iProver_top ),
% 3.26/1.00      inference(forward_subsumption_resolution,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_13958,c_7145]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_13966,plain,
% 3.26/1.00      ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,X0)) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_7117,c_13962]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_13968,plain,
% 3.26/1.00      ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_13966]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7112,plain,
% 3.26/1.00      ( r2_hidden(sK10,k1_funct_2(sK8,sK9)) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12777,plain,
% 3.26/1.00      ( r2_hidden(sK10,k1_funct_2(sK8,k1_xboole_0)) != iProver_top ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_12756,c_7112]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12787,plain,
% 3.26/1.00      ( r2_hidden(sK10,k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.26/1.00      inference(light_normalisation,[status(thm)],[c_12777,c_12780]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_13520,plain,
% 3.26/1.00      ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_13514,c_12787]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(contradiction,plain,
% 3.26/1.00      ( $false ),
% 3.26/1.00      inference(minisat,[status(thm)],[c_13968,c_13520]) ).
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.26/1.00  
% 3.26/1.00  ------                               Statistics
% 3.26/1.00  
% 3.26/1.00  ------ General
% 3.26/1.00  
% 3.26/1.00  abstr_ref_over_cycles:                  0
% 3.26/1.00  abstr_ref_under_cycles:                 0
% 3.26/1.00  gc_basic_clause_elim:                   0
% 3.26/1.00  forced_gc_time:                         0
% 3.26/1.00  parsing_time:                           0.017
% 3.26/1.00  unif_index_cands_time:                  0.
% 3.26/1.00  unif_index_add_time:                    0.
% 3.26/1.00  orderings_time:                         0.
% 3.26/1.00  out_proof_time:                         0.014
% 3.26/1.00  total_time:                             0.311
% 3.26/1.00  num_of_symbols:                         59
% 3.26/1.00  num_of_terms:                           9927
% 3.26/1.00  
% 3.26/1.00  ------ Preprocessing
% 3.26/1.00  
% 3.26/1.00  num_of_splits:                          0
% 3.26/1.00  num_of_split_atoms:                     0
% 3.26/1.00  num_of_reused_defs:                     0
% 3.26/1.00  num_eq_ax_congr_red:                    61
% 3.26/1.00  num_of_sem_filtered_clauses:            1
% 3.26/1.00  num_of_subtypes:                        0
% 3.26/1.00  monotx_restored_types:                  0
% 3.26/1.00  sat_num_of_epr_types:                   0
% 3.26/1.00  sat_num_of_non_cyclic_types:            0
% 3.26/1.00  sat_guarded_non_collapsed_types:        0
% 3.26/1.00  num_pure_diseq_elim:                    0
% 3.26/1.00  simp_replaced_by:                       0
% 3.26/1.00  res_preprocessed:                       269
% 3.26/1.00  prep_upred:                             0
% 3.26/1.00  prep_unflattend:                        258
% 3.26/1.00  smt_new_axioms:                         0
% 3.26/1.00  pred_elim_cands:                        7
% 3.26/1.00  pred_elim:                              3
% 3.26/1.00  pred_elim_cl:                           6
% 3.26/1.00  pred_elim_cycles:                       9
% 3.26/1.00  merged_defs:                            8
% 3.26/1.00  merged_defs_ncl:                        0
% 3.26/1.00  bin_hyper_res:                          8
% 3.26/1.00  prep_cycles:                            4
% 3.26/1.00  pred_elim_time:                         0.081
% 3.26/1.00  splitting_time:                         0.
% 3.26/1.00  sem_filter_time:                        0.
% 3.26/1.00  monotx_time:                            0.
% 3.26/1.00  subtype_inf_time:                       0.
% 3.26/1.00  
% 3.26/1.00  ------ Problem properties
% 3.26/1.00  
% 3.26/1.00  clauses:                                57
% 3.26/1.00  conjectures:                            4
% 3.26/1.00  epr:                                    7
% 3.26/1.00  horn:                                   41
% 3.26/1.00  ground:                                 7
% 3.26/1.00  unary:                                  18
% 3.26/1.00  binary:                                 17
% 3.26/1.00  lits:                                   128
% 3.26/1.00  lits_eq:                                36
% 3.26/1.00  fd_pure:                                0
% 3.26/1.00  fd_pseudo:                              0
% 3.26/1.00  fd_cond:                                5
% 3.26/1.00  fd_pseudo_cond:                         2
% 3.26/1.00  ac_symbols:                             0
% 3.26/1.00  
% 3.26/1.00  ------ Propositional Solver
% 3.26/1.00  
% 3.26/1.00  prop_solver_calls:                      28
% 3.26/1.00  prop_fast_solver_calls:                 2698
% 3.26/1.00  smt_solver_calls:                       0
% 3.26/1.00  smt_fast_solver_calls:                  0
% 3.26/1.00  prop_num_of_clauses:                    3696
% 3.26/1.00  prop_preprocess_simplified:             12650
% 3.26/1.00  prop_fo_subsumed:                       81
% 3.26/1.00  prop_solver_time:                       0.
% 3.26/1.00  smt_solver_time:                        0.
% 3.26/1.00  smt_fast_solver_time:                   0.
% 3.26/1.00  prop_fast_solver_time:                  0.
% 3.26/1.00  prop_unsat_core_time:                   0.
% 3.26/1.00  
% 3.26/1.00  ------ QBF
% 3.26/1.00  
% 3.26/1.00  qbf_q_res:                              0
% 3.26/1.00  qbf_num_tautologies:                    0
% 3.26/1.00  qbf_prep_cycles:                        0
% 3.26/1.00  
% 3.26/1.00  ------ BMC1
% 3.26/1.00  
% 3.26/1.00  bmc1_current_bound:                     -1
% 3.26/1.00  bmc1_last_solved_bound:                 -1
% 3.26/1.00  bmc1_unsat_core_size:                   -1
% 3.26/1.00  bmc1_unsat_core_parents_size:           -1
% 3.26/1.00  bmc1_merge_next_fun:                    0
% 3.26/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.26/1.00  
% 3.26/1.00  ------ Instantiation
% 3.26/1.00  
% 3.26/1.00  inst_num_of_clauses:                    849
% 3.26/1.00  inst_num_in_passive:                    183
% 3.26/1.00  inst_num_in_active:                     450
% 3.26/1.00  inst_num_in_unprocessed:                216
% 3.26/1.00  inst_num_of_loops:                      610
% 3.26/1.00  inst_num_of_learning_restarts:          0
% 3.26/1.00  inst_num_moves_active_passive:          157
% 3.26/1.00  inst_lit_activity:                      0
% 3.26/1.00  inst_lit_activity_moves:                0
% 3.26/1.00  inst_num_tautologies:                   0
% 3.26/1.00  inst_num_prop_implied:                  0
% 3.26/1.00  inst_num_existing_simplified:           0
% 3.26/1.00  inst_num_eq_res_simplified:             0
% 3.26/1.00  inst_num_child_elim:                    0
% 3.26/1.00  inst_num_of_dismatching_blockings:      386
% 3.26/1.00  inst_num_of_non_proper_insts:           795
% 3.26/1.00  inst_num_of_duplicates:                 0
% 3.26/1.00  inst_inst_num_from_inst_to_res:         0
% 3.26/1.00  inst_dismatching_checking_time:         0.
% 3.26/1.00  
% 3.26/1.00  ------ Resolution
% 3.26/1.00  
% 3.26/1.00  res_num_of_clauses:                     0
% 3.26/1.00  res_num_in_passive:                     0
% 3.26/1.00  res_num_in_active:                      0
% 3.26/1.00  res_num_of_loops:                       273
% 3.26/1.00  res_forward_subset_subsumed:            32
% 3.26/1.00  res_backward_subset_subsumed:           10
% 3.26/1.00  res_forward_subsumed:                   0
% 3.26/1.00  res_backward_subsumed:                  0
% 3.26/1.00  res_forward_subsumption_resolution:     8
% 3.26/1.00  res_backward_subsumption_resolution:    0
% 3.26/1.00  res_clause_to_clause_subsumption:       986
% 3.26/1.00  res_orphan_elimination:                 0
% 3.26/1.00  res_tautology_del:                      88
% 3.26/1.00  res_num_eq_res_simplified:              0
% 3.26/1.00  res_num_sel_changes:                    0
% 3.26/1.00  res_moves_from_active_to_pass:          0
% 3.26/1.00  
% 3.26/1.00  ------ Superposition
% 3.26/1.00  
% 3.26/1.00  sup_time_total:                         0.
% 3.26/1.00  sup_time_generating:                    0.
% 3.26/1.00  sup_time_sim_full:                      0.
% 3.26/1.00  sup_time_sim_immed:                     0.
% 3.26/1.00  
% 3.26/1.00  sup_num_of_clauses:                     192
% 3.26/1.00  sup_num_in_active:                      80
% 3.26/1.00  sup_num_in_passive:                     112
% 3.26/1.00  sup_num_of_loops:                       121
% 3.26/1.00  sup_fw_superposition:                   149
% 3.26/1.00  sup_bw_superposition:                   55
% 3.26/1.00  sup_immediate_simplified:               60
% 3.26/1.00  sup_given_eliminated:                   0
% 3.26/1.00  comparisons_done:                       0
% 3.26/1.00  comparisons_avoided:                    19
% 3.26/1.00  
% 3.26/1.00  ------ Simplifications
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  sim_fw_subset_subsumed:                 11
% 3.26/1.00  sim_bw_subset_subsumed:                 11
% 3.26/1.00  sim_fw_subsumed:                        11
% 3.26/1.00  sim_bw_subsumed:                        0
% 3.26/1.00  sim_fw_subsumption_res:                 2
% 3.26/1.00  sim_bw_subsumption_res:                 0
% 3.26/1.00  sim_tautology_del:                      6
% 3.26/1.00  sim_eq_tautology_del:                   6
% 3.26/1.00  sim_eq_res_simp:                        3
% 3.26/1.00  sim_fw_demodulated:                     25
% 3.26/1.00  sim_bw_demodulated:                     39
% 3.26/1.00  sim_light_normalised:                   26
% 3.26/1.00  sim_joinable_taut:                      0
% 3.26/1.00  sim_joinable_simp:                      0
% 3.26/1.00  sim_ac_normalised:                      0
% 3.26/1.00  sim_smt_subsumption:                    0
% 3.26/1.00  
%------------------------------------------------------------------------------

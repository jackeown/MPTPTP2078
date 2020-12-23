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
% DateTime   : Thu Dec  3 12:00:44 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 7.84s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 640 expanded)
%              Number of clauses        :  110 ( 251 expanded)
%              Number of leaves         :   27 ( 141 expanded)
%              Depth                    :   21
%              Number of atoms          :  613 (2935 expanded)
%              Number of equality atoms :  340 (1225 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,axiom,(
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

fof(f66,plain,(
    ! [X1,X0,X2] :
      ( sP2(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP2(X1,X0,X2) ) ),
    inference(definition_folding,[],[f29,f66])).

fof(f95,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP2(X1,X0,X2) )
      & ( sP2(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f95])).

fof(f193,plain,(
    ! [X0,X1] : sP2(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f169])).

fof(f30,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f61,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f62,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f61])).

fof(f96,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(sK15,k1_funct_2(sK13,sK14))
      & ( k1_xboole_0 = sK13
        | k1_xboole_0 != sK14 )
      & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
      & v1_funct_2(sK15,sK13,sK14)
      & v1_funct_1(sK15) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,
    ( ~ r2_hidden(sK15,k1_funct_2(sK13,sK14))
    & ( k1_xboole_0 = sK13
      | k1_xboole_0 != sK14 )
    & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
    & v1_funct_2(sK15,sK13,sK14)
    & v1_funct_1(sK15) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f62,f96])).

fof(f173,plain,(
    m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) ),
    inference(cnf_transformation,[],[f97])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f28,axiom,(
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

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f88,plain,(
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
    inference(nnf_transformation,[],[f60])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f172,plain,(
    v1_funct_2(sK15,sK13,sK14) ),
    inference(cnf_transformation,[],[f97])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
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
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f66])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
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
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f89])).

fof(f93,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X0)
          & k1_relat_1(X8) = X1
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK12(X0,X1,X6)),X0)
        & k1_relat_1(sK12(X0,X1,X6)) = X1
        & sK12(X0,X1,X6) = X6
        & v1_funct_1(sK12(X0,X1,X6))
        & v1_relat_1(sK12(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f92,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X0)
          & k1_relat_1(X5) = X1
          & X3 = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK11(X0,X1,X2)),X0)
        & k1_relat_1(sK11(X0,X1,X2)) = X1
        & sK11(X0,X1,X2) = X3
        & v1_funct_1(sK11(X0,X1,X2))
        & v1_relat_1(sK11(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
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
              | sK10(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X0)
              & k1_relat_1(X5) = X1
              & sK10(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | k1_relat_1(X4) != X1
                | sK10(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK11(X0,X1,X2)),X0)
              & k1_relat_1(sK11(X0,X1,X2)) = X1
              & sK10(X0,X1,X2) = sK11(X0,X1,X2)
              & v1_funct_1(sK11(X0,X1,X2))
              & v1_relat_1(sK11(X0,X1,X2)) )
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | k1_relat_1(X7) != X1
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK12(X0,X1,X6)),X0)
                & k1_relat_1(sK12(X0,X1,X6)) = X1
                & sK12(X0,X1,X6) = X6
                & v1_funct_1(sK12(X0,X1,X6))
                & v1_relat_1(sK12(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f90,f93,f92,f91])).

fof(f162,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_tarski(k2_relat_1(X7),X0)
      | k1_relat_1(X7) != X1
      | X6 != X7
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f191,plain,(
    ! [X6,X2,X0,X7] :
      ( r2_hidden(X6,X2)
      | ~ r1_tarski(k2_relat_1(X7),X0)
      | X6 != X7
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | ~ sP2(X0,k1_relat_1(X7),X2) ) ),
    inference(equality_resolution,[],[f162])).

fof(f192,plain,(
    ! [X2,X0,X7] :
      ( r2_hidden(X7,X2)
      | ~ r1_tarski(k2_relat_1(X7),X0)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | ~ sP2(X0,k1_relat_1(X7),X2) ) ),
    inference(equality_resolution,[],[f191])).

fof(f171,plain,(
    v1_funct_1(sK15) ),
    inference(cnf_transformation,[],[f97])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f175,plain,(
    ~ r2_hidden(sK15,k1_funct_2(sK13,sK14)) ),
    inference(cnf_transformation,[],[f97])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_2(X0,X1) = X2
      | ~ sP2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f101,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f177,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f99,f101])).

fof(f174,plain,
    ( k1_xboole_0 = sK13
    | k1_xboole_0 != sK14 ),
    inference(cnf_transformation,[],[f97])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f100,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f178,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f100,f101])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f72])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f73])).

fof(f184,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f108])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f77,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f121,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f14,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f119,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_4434,plain,
    ( ~ sP2(X0,X1,X2)
    | sP2(X0,X3,X4)
    | X3 != X1
    | X4 != X2 ),
    theory(equality)).

cnf(c_17634,plain,
    ( ~ sP2(X0,X1,X2)
    | sP2(X0,k1_relat_1(sK15),k1_funct_2(sK13,sK14))
    | k1_funct_2(sK13,sK14) != X2
    | k1_relat_1(sK15) != X1 ),
    inference(instantiation,[status(thm)],[c_4434])).

cnf(c_32712,plain,
    ( ~ sP2(X0,X1,k1_funct_2(X2,X3))
    | sP2(X0,k1_relat_1(sK15),k1_funct_2(sK13,sK14))
    | k1_funct_2(sK13,sK14) != k1_funct_2(X2,X3)
    | k1_relat_1(sK15) != X1 ),
    inference(instantiation,[status(thm)],[c_17634])).

cnf(c_32714,plain,
    ( sP2(k1_xboole_0,k1_relat_1(sK15),k1_funct_2(sK13,sK14))
    | ~ sP2(k1_xboole_0,k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))
    | k1_funct_2(sK13,sK14) != k1_funct_2(k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK15) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_32712])).

cnf(c_4417,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_14443,plain,
    ( X0 != X1
    | X0 = k2_relat_1(X2)
    | k2_relat_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_4417])).

cnf(c_14444,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14443])).

cnf(c_70,plain,
    ( sP2(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f193])).

cnf(c_5659,plain,
    ( sP2(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_73,negated_conjecture,
    ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) ),
    inference(cnf_transformation,[],[f173])).

cnf(c_5657,plain,
    ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_46,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_5677,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_9708,plain,
    ( k2_relset_1(sK13,sK14,sK15) = k2_relat_1(sK15) ),
    inference(superposition,[status(thm)],[c_5657,c_5677])).

cnf(c_44,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_5679,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_11506,plain,
    ( m1_subset_1(k2_relat_1(sK15),k1_zfmisc_1(sK14)) = iProver_top
    | m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9708,c_5679])).

cnf(c_78,plain,
    ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_11658,plain,
    ( m1_subset_1(k2_relat_1(sK15),k1_zfmisc_1(sK14)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11506,c_78])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_5701,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11662,plain,
    ( r1_tarski(k2_relat_1(sK15),sK14) = iProver_top ),
    inference(superposition,[status(thm)],[c_11658,c_5701])).

cnf(c_56,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f151])).

cnf(c_74,negated_conjecture,
    ( v1_funct_2(sK15,sK13,sK14) ),
    inference(cnf_transformation,[],[f172])).

cnf(c_994,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK14 != X2
    | sK13 != X1
    | sK15 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_56,c_74])).

cnf(c_995,plain,
    ( ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
    | k1_relset_1(sK13,sK14,sK15) = sK13
    | k1_xboole_0 = sK14 ),
    inference(unflattening,[status(thm)],[c_994])).

cnf(c_997,plain,
    ( k1_relset_1(sK13,sK14,sK15) = sK13
    | k1_xboole_0 = sK14 ),
    inference(global_propositional_subsumption,[status(thm)],[c_995,c_73])).

cnf(c_45,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_5678,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_10500,plain,
    ( k1_relset_1(sK13,sK14,sK15) = k1_relat_1(sK15) ),
    inference(superposition,[status(thm)],[c_5657,c_5678])).

cnf(c_11094,plain,
    ( k1_relat_1(sK15) = sK13
    | sK14 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_997,c_10500])).

cnf(c_63,plain,
    ( ~ sP2(X0,k1_relat_1(X1),X2)
    | r2_hidden(X1,X2)
    | ~ r1_tarski(k2_relat_1(X1),X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f192])).

cnf(c_5666,plain,
    ( sP2(X0,k1_relat_1(X1),X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_13013,plain,
    ( sK14 = k1_xboole_0
    | sP2(X0,sK13,X1) != iProver_top
    | r2_hidden(sK15,X1) = iProver_top
    | r1_tarski(k2_relat_1(sK15),X0) != iProver_top
    | v1_funct_1(sK15) != iProver_top
    | v1_relat_1(sK15) != iProver_top ),
    inference(superposition,[status(thm)],[c_11094,c_5666])).

cnf(c_75,negated_conjecture,
    ( v1_funct_1(sK15) ),
    inference(cnf_transformation,[],[f171])).

cnf(c_76,plain,
    ( v1_funct_1(sK15) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_75])).

cnf(c_41,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_5794,plain,
    ( ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK15) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_5840,plain,
    ( ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
    | v1_relat_1(sK15) ),
    inference(instantiation,[status(thm)],[c_5794])).

cnf(c_5841,plain,
    ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) != iProver_top
    | v1_relat_1(sK15) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5840])).

cnf(c_13679,plain,
    ( sK14 = k1_xboole_0
    | sP2(X0,sK13,X1) != iProver_top
    | r2_hidden(sK15,X1) = iProver_top
    | r1_tarski(k2_relat_1(sK15),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13013,c_76,c_78,c_5841])).

cnf(c_13685,plain,
    ( sK14 = k1_xboole_0
    | sP2(sK14,sK13,X0) != iProver_top
    | r2_hidden(sK15,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11662,c_13679])).

cnf(c_71,negated_conjecture,
    ( ~ r2_hidden(sK15,k1_funct_2(sK13,sK14)) ),
    inference(cnf_transformation,[],[f175])).

cnf(c_79,plain,
    ( r2_hidden(sK15,k1_funct_2(sK13,sK14)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_4421,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5778,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK15,k1_funct_2(sK13,sK14))
    | k1_funct_2(sK13,sK14) != X1
    | sK15 != X0 ),
    inference(instantiation,[status(thm)],[c_4421])).

cnf(c_5819,plain,
    ( ~ r2_hidden(sK15,X0)
    | r2_hidden(sK15,k1_funct_2(sK13,sK14))
    | k1_funct_2(sK13,sK14) != X0
    | sK15 != sK15 ),
    inference(instantiation,[status(thm)],[c_5778])).

cnf(c_5820,plain,
    ( k1_funct_2(sK13,sK14) != X0
    | sK15 != sK15
    | r2_hidden(sK15,X0) != iProver_top
    | r2_hidden(sK15,k1_funct_2(sK13,sK14)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5819])).

cnf(c_4416,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5871,plain,
    ( sK15 = sK15 ),
    inference(instantiation,[status(thm)],[c_4416])).

cnf(c_69,plain,
    ( ~ sP2(X0,X1,X2)
    | k1_funct_2(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f170])).

cnf(c_7688,plain,
    ( ~ sP2(sK14,sK13,X0)
    | k1_funct_2(sK13,sK14) = X0 ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_7689,plain,
    ( k1_funct_2(sK13,sK14) = X0
    | sP2(sK14,sK13,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7688])).

cnf(c_13774,plain,
    ( sP2(sK14,sK13,X0) != iProver_top
    | sK14 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13685,c_79,c_5820,c_5871,c_7689])).

cnf(c_13775,plain,
    ( sK14 = k1_xboole_0
    | sP2(sK14,sK13,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13774])).

cnf(c_13780,plain,
    ( sK14 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5659,c_13775])).

cnf(c_6991,plain,
    ( r1_tarski(sK15,k2_zfmisc_1(sK13,sK14)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5657,c_5701])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f177])).

cnf(c_5707,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8624,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK15,k2_zfmisc_1(sK13,sK14))) = sK15 ),
    inference(superposition,[status(thm)],[c_6991,c_5707])).

cnf(c_13794,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK15,k2_zfmisc_1(sK13,k1_xboole_0))) = sK15 ),
    inference(demodulation,[status(thm)],[c_13780,c_8624])).

cnf(c_72,negated_conjecture,
    ( k1_xboole_0 != sK14
    | k1_xboole_0 = sK13 ),
    inference(cnf_transformation,[],[f174])).

cnf(c_13801,plain,
    ( sK13 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13780,c_72])).

cnf(c_13802,plain,
    ( sK13 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_13801])).

cnf(c_13811,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK15,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = sK15 ),
    inference(demodulation,[status(thm)],[c_13794,c_13802])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f178])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f184])).

cnf(c_13812,plain,
    ( sK15 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13811,c_2,c_8])).

cnf(c_13459,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(X2,X3)
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_4417])).

cnf(c_13460,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13459])).

cnf(c_4419,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_10519,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK15,k2_zfmisc_1(X2,X3))
    | X1 != k2_zfmisc_1(X2,X3)
    | X0 != sK15 ),
    inference(instantiation,[status(thm)],[c_4419])).

cnf(c_10528,plain,
    ( ~ r1_tarski(sK15,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK15 ),
    inference(instantiation,[status(thm)],[c_10519])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_9625,plain,
    ( ~ v1_relat_1(sK15)
    | k1_relat_1(sK15) = k1_xboole_0
    | k2_relat_1(sK15) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_4436,plain,
    ( X0 != X1
    | X2 != X3
    | k1_funct_2(X0,X2) = k1_funct_2(X1,X3) ),
    theory(equality)).

cnf(c_9168,plain,
    ( k1_funct_2(sK13,sK14) = k1_funct_2(X0,X1)
    | sK14 != X1
    | sK13 != X0 ),
    inference(instantiation,[status(thm)],[c_4436])).

cnf(c_9169,plain,
    ( k1_funct_2(sK13,sK14) = k1_funct_2(k1_xboole_0,k1_xboole_0)
    | sK14 != k1_xboole_0
    | sK13 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9168])).

cnf(c_8659,plain,
    ( sK14 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK14 ),
    inference(instantiation,[status(thm)],[c_4417])).

cnf(c_8660,plain,
    ( sK14 != k1_xboole_0
    | k1_xboole_0 = sK14
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8659])).

cnf(c_6072,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK15,k2_zfmisc_1(X2,X3))
    | k2_zfmisc_1(X2,X3) != X1
    | sK15 != X0 ),
    inference(instantiation,[status(thm)],[c_4419])).

cnf(c_6525,plain,
    ( ~ r1_tarski(sK15,X0)
    | r1_tarski(sK15,k2_zfmisc_1(X1,X2))
    | k2_zfmisc_1(X1,X2) != X0
    | sK15 != sK15 ),
    inference(instantiation,[status(thm)],[c_6072])).

cnf(c_7133,plain,
    ( r1_tarski(sK15,k2_zfmisc_1(X0,X1))
    | ~ r1_tarski(sK15,k2_zfmisc_1(sK13,sK14))
    | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK13,sK14)
    | sK15 != sK15 ),
    inference(instantiation,[status(thm)],[c_6525])).

cnf(c_7135,plain,
    ( ~ r1_tarski(sK15,k2_zfmisc_1(sK13,sK14))
    | r1_tarski(sK15,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK13,sK14)
    | sK15 != sK15 ),
    inference(instantiation,[status(thm)],[c_7133])).

cnf(c_4427,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_7046,plain,
    ( k2_relat_1(sK15) = k2_relat_1(X0)
    | sK15 != X0 ),
    inference(instantiation,[status(thm)],[c_4427])).

cnf(c_7047,plain,
    ( k2_relat_1(sK15) = k2_relat_1(k1_xboole_0)
    | sK15 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7046])).

cnf(c_6259,plain,
    ( X0 != X1
    | k2_relat_1(sK15) != X1
    | k2_relat_1(sK15) = X0 ),
    inference(instantiation,[status(thm)],[c_4417])).

cnf(c_7012,plain,
    ( X0 != k2_relat_1(X1)
    | k2_relat_1(sK15) = X0
    | k2_relat_1(sK15) != k2_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_6259])).

cnf(c_7013,plain,
    ( k2_relat_1(sK15) != k2_relat_1(k1_xboole_0)
    | k2_relat_1(sK15) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7012])).

cnf(c_4422,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_6708,plain,
    ( X0 != sK14
    | X1 != sK13
    | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK13,sK14) ),
    inference(instantiation,[status(thm)],[c_4422])).

cnf(c_6709,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK13,sK14)
    | k1_xboole_0 != sK14
    | k1_xboole_0 != sK13 ),
    inference(instantiation,[status(thm)],[c_6708])).

cnf(c_6063,plain,
    ( ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r1_tarski(sK15,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_6467,plain,
    ( ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
    | r1_tarski(sK15,k2_zfmisc_1(sK13,sK14)) ),
    inference(instantiation,[status(thm)],[c_6063])).

cnf(c_6056,plain,
    ( X0 != X1
    | X0 = sK15
    | sK15 != X1 ),
    inference(instantiation,[status(thm)],[c_4417])).

cnf(c_6057,plain,
    ( sK15 != k1_xboole_0
    | k1_xboole_0 = sK15
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6056])).

cnf(c_5977,plain,
    ( sK13 = sK13 ),
    inference(instantiation,[status(thm)],[c_4416])).

cnf(c_5947,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK15),X2)
    | X2 != X1
    | k2_relat_1(sK15) != X0 ),
    inference(instantiation,[status(thm)],[c_4419])).

cnf(c_5949,plain,
    ( r1_tarski(k2_relat_1(sK15),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k2_relat_1(sK15) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5947])).

cnf(c_5793,plain,
    ( sK13 != X0
    | sK13 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_4417])).

cnf(c_5838,plain,
    ( sK13 != sK13
    | sK13 = k1_xboole_0
    | k1_xboole_0 != sK13 ),
    inference(instantiation,[status(thm)],[c_5793])).

cnf(c_5773,plain,
    ( ~ sP2(X0,k1_relat_1(sK15),k1_funct_2(sK13,sK14))
    | r2_hidden(sK15,k1_funct_2(sK13,sK14))
    | ~ r1_tarski(k2_relat_1(sK15),X0)
    | ~ v1_funct_1(sK15)
    | ~ v1_relat_1(sK15) ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_5775,plain,
    ( ~ sP2(k1_xboole_0,k1_relat_1(sK15),k1_funct_2(sK13,sK14))
    | r2_hidden(sK15,k1_funct_2(sK13,sK14))
    | ~ r1_tarski(k2_relat_1(sK15),k1_xboole_0)
    | ~ v1_funct_1(sK15)
    | ~ v1_relat_1(sK15) ),
    inference(instantiation,[status(thm)],[c_5773])).

cnf(c_252,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_251,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_18,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_81,plain,
    ( sP2(k1_xboole_0,k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32714,c_14444,c_13812,c_13780,c_13460,c_10528,c_9625,c_9169,c_8660,c_7135,c_7047,c_7013,c_6709,c_6467,c_6057,c_5977,c_5949,c_5871,c_5840,c_5838,c_5775,c_252,c_251,c_18,c_81,c_71,c_72,c_73,c_75])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:19:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.84/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.84/1.51  
% 7.84/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.84/1.51  
% 7.84/1.51  ------  iProver source info
% 7.84/1.51  
% 7.84/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.84/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.84/1.51  git: non_committed_changes: false
% 7.84/1.51  git: last_make_outside_of_git: false
% 7.84/1.51  
% 7.84/1.51  ------ 
% 7.84/1.51  
% 7.84/1.51  ------ Input Options
% 7.84/1.51  
% 7.84/1.51  --out_options                           all
% 7.84/1.51  --tptp_safe_out                         true
% 7.84/1.51  --problem_path                          ""
% 7.84/1.51  --include_path                          ""
% 7.84/1.51  --clausifier                            res/vclausify_rel
% 7.84/1.51  --clausifier_options                    ""
% 7.84/1.51  --stdin                                 false
% 7.84/1.51  --stats_out                             all
% 7.84/1.51  
% 7.84/1.51  ------ General Options
% 7.84/1.51  
% 7.84/1.51  --fof                                   false
% 7.84/1.51  --time_out_real                         305.
% 7.84/1.51  --time_out_virtual                      -1.
% 7.84/1.51  --symbol_type_check                     false
% 7.84/1.51  --clausify_out                          false
% 7.84/1.51  --sig_cnt_out                           false
% 7.84/1.51  --trig_cnt_out                          false
% 7.84/1.51  --trig_cnt_out_tolerance                1.
% 7.84/1.51  --trig_cnt_out_sk_spl                   false
% 7.84/1.51  --abstr_cl_out                          false
% 7.84/1.51  
% 7.84/1.51  ------ Global Options
% 7.84/1.51  
% 7.84/1.51  --schedule                              default
% 7.84/1.51  --add_important_lit                     false
% 7.84/1.51  --prop_solver_per_cl                    1000
% 7.84/1.51  --min_unsat_core                        false
% 7.84/1.51  --soft_assumptions                      false
% 7.84/1.51  --soft_lemma_size                       3
% 7.84/1.51  --prop_impl_unit_size                   0
% 7.84/1.51  --prop_impl_unit                        []
% 7.84/1.51  --share_sel_clauses                     true
% 7.84/1.51  --reset_solvers                         false
% 7.84/1.51  --bc_imp_inh                            [conj_cone]
% 7.84/1.51  --conj_cone_tolerance                   3.
% 7.84/1.51  --extra_neg_conj                        none
% 7.84/1.51  --large_theory_mode                     true
% 7.84/1.51  --prolific_symb_bound                   200
% 7.84/1.51  --lt_threshold                          2000
% 7.84/1.51  --clause_weak_htbl                      true
% 7.84/1.51  --gc_record_bc_elim                     false
% 7.84/1.51  
% 7.84/1.51  ------ Preprocessing Options
% 7.84/1.51  
% 7.84/1.51  --preprocessing_flag                    true
% 7.84/1.51  --time_out_prep_mult                    0.1
% 7.84/1.51  --splitting_mode                        input
% 7.84/1.51  --splitting_grd                         true
% 7.84/1.51  --splitting_cvd                         false
% 7.84/1.51  --splitting_cvd_svl                     false
% 7.84/1.51  --splitting_nvd                         32
% 7.84/1.51  --sub_typing                            true
% 7.84/1.51  --prep_gs_sim                           true
% 7.84/1.51  --prep_unflatten                        true
% 7.84/1.51  --prep_res_sim                          true
% 7.84/1.51  --prep_upred                            true
% 7.84/1.51  --prep_sem_filter                       exhaustive
% 7.84/1.51  --prep_sem_filter_out                   false
% 7.84/1.51  --pred_elim                             true
% 7.84/1.51  --res_sim_input                         true
% 7.84/1.51  --eq_ax_congr_red                       true
% 7.84/1.51  --pure_diseq_elim                       true
% 7.84/1.51  --brand_transform                       false
% 7.84/1.51  --non_eq_to_eq                          false
% 7.84/1.51  --prep_def_merge                        true
% 7.84/1.51  --prep_def_merge_prop_impl              false
% 7.84/1.51  --prep_def_merge_mbd                    true
% 7.84/1.51  --prep_def_merge_tr_red                 false
% 7.84/1.51  --prep_def_merge_tr_cl                  false
% 7.84/1.51  --smt_preprocessing                     true
% 7.84/1.51  --smt_ac_axioms                         fast
% 7.84/1.51  --preprocessed_out                      false
% 7.84/1.51  --preprocessed_stats                    false
% 7.84/1.51  
% 7.84/1.51  ------ Abstraction refinement Options
% 7.84/1.51  
% 7.84/1.51  --abstr_ref                             []
% 7.84/1.51  --abstr_ref_prep                        false
% 7.84/1.51  --abstr_ref_until_sat                   false
% 7.84/1.51  --abstr_ref_sig_restrict                funpre
% 7.84/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.84/1.51  --abstr_ref_under                       []
% 7.84/1.51  
% 7.84/1.51  ------ SAT Options
% 7.84/1.51  
% 7.84/1.51  --sat_mode                              false
% 7.84/1.51  --sat_fm_restart_options                ""
% 7.84/1.51  --sat_gr_def                            false
% 7.84/1.51  --sat_epr_types                         true
% 7.84/1.51  --sat_non_cyclic_types                  false
% 7.84/1.51  --sat_finite_models                     false
% 7.84/1.51  --sat_fm_lemmas                         false
% 7.84/1.51  --sat_fm_prep                           false
% 7.84/1.51  --sat_fm_uc_incr                        true
% 7.84/1.51  --sat_out_model                         small
% 7.84/1.51  --sat_out_clauses                       false
% 7.84/1.51  
% 7.84/1.51  ------ QBF Options
% 7.84/1.51  
% 7.84/1.51  --qbf_mode                              false
% 7.84/1.51  --qbf_elim_univ                         false
% 7.84/1.51  --qbf_dom_inst                          none
% 7.84/1.51  --qbf_dom_pre_inst                      false
% 7.84/1.51  --qbf_sk_in                             false
% 7.84/1.51  --qbf_pred_elim                         true
% 7.84/1.51  --qbf_split                             512
% 7.84/1.51  
% 7.84/1.51  ------ BMC1 Options
% 7.84/1.51  
% 7.84/1.51  --bmc1_incremental                      false
% 7.84/1.51  --bmc1_axioms                           reachable_all
% 7.84/1.51  --bmc1_min_bound                        0
% 7.84/1.51  --bmc1_max_bound                        -1
% 7.84/1.51  --bmc1_max_bound_default                -1
% 7.84/1.51  --bmc1_symbol_reachability              true
% 7.84/1.51  --bmc1_property_lemmas                  false
% 7.84/1.51  --bmc1_k_induction                      false
% 7.84/1.51  --bmc1_non_equiv_states                 false
% 7.84/1.51  --bmc1_deadlock                         false
% 7.84/1.51  --bmc1_ucm                              false
% 7.84/1.51  --bmc1_add_unsat_core                   none
% 7.84/1.51  --bmc1_unsat_core_children              false
% 7.84/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.84/1.51  --bmc1_out_stat                         full
% 7.84/1.51  --bmc1_ground_init                      false
% 7.84/1.51  --bmc1_pre_inst_next_state              false
% 7.84/1.51  --bmc1_pre_inst_state                   false
% 7.84/1.51  --bmc1_pre_inst_reach_state             false
% 7.84/1.51  --bmc1_out_unsat_core                   false
% 7.84/1.51  --bmc1_aig_witness_out                  false
% 7.84/1.51  --bmc1_verbose                          false
% 7.84/1.51  --bmc1_dump_clauses_tptp                false
% 7.84/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.84/1.51  --bmc1_dump_file                        -
% 7.84/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.84/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.84/1.51  --bmc1_ucm_extend_mode                  1
% 7.84/1.51  --bmc1_ucm_init_mode                    2
% 7.84/1.51  --bmc1_ucm_cone_mode                    none
% 7.84/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.84/1.51  --bmc1_ucm_relax_model                  4
% 7.84/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.84/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.84/1.51  --bmc1_ucm_layered_model                none
% 7.84/1.51  --bmc1_ucm_max_lemma_size               10
% 7.84/1.51  
% 7.84/1.51  ------ AIG Options
% 7.84/1.51  
% 7.84/1.51  --aig_mode                              false
% 7.84/1.51  
% 7.84/1.51  ------ Instantiation Options
% 7.84/1.51  
% 7.84/1.51  --instantiation_flag                    true
% 7.84/1.51  --inst_sos_flag                         true
% 7.84/1.51  --inst_sos_phase                        true
% 7.84/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.84/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.84/1.51  --inst_lit_sel_side                     num_symb
% 7.84/1.51  --inst_solver_per_active                1400
% 7.84/1.51  --inst_solver_calls_frac                1.
% 7.84/1.51  --inst_passive_queue_type               priority_queues
% 7.84/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.84/1.51  --inst_passive_queues_freq              [25;2]
% 7.84/1.51  --inst_dismatching                      true
% 7.84/1.51  --inst_eager_unprocessed_to_passive     true
% 7.84/1.51  --inst_prop_sim_given                   true
% 7.84/1.51  --inst_prop_sim_new                     false
% 7.84/1.51  --inst_subs_new                         false
% 7.84/1.51  --inst_eq_res_simp                      false
% 7.84/1.51  --inst_subs_given                       false
% 7.84/1.51  --inst_orphan_elimination               true
% 7.84/1.51  --inst_learning_loop_flag               true
% 7.84/1.51  --inst_learning_start                   3000
% 7.84/1.51  --inst_learning_factor                  2
% 7.84/1.51  --inst_start_prop_sim_after_learn       3
% 7.84/1.51  --inst_sel_renew                        solver
% 7.84/1.51  --inst_lit_activity_flag                true
% 7.84/1.51  --inst_restr_to_given                   false
% 7.84/1.51  --inst_activity_threshold               500
% 7.84/1.51  --inst_out_proof                        true
% 7.84/1.51  
% 7.84/1.51  ------ Resolution Options
% 7.84/1.51  
% 7.84/1.51  --resolution_flag                       true
% 7.84/1.51  --res_lit_sel                           adaptive
% 7.84/1.51  --res_lit_sel_side                      none
% 7.84/1.51  --res_ordering                          kbo
% 7.84/1.51  --res_to_prop_solver                    active
% 7.84/1.51  --res_prop_simpl_new                    false
% 7.84/1.51  --res_prop_simpl_given                  true
% 7.84/1.51  --res_passive_queue_type                priority_queues
% 7.84/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.84/1.51  --res_passive_queues_freq               [15;5]
% 7.84/1.51  --res_forward_subs                      full
% 7.84/1.51  --res_backward_subs                     full
% 7.84/1.51  --res_forward_subs_resolution           true
% 7.84/1.51  --res_backward_subs_resolution          true
% 7.84/1.51  --res_orphan_elimination                true
% 7.84/1.51  --res_time_limit                        2.
% 7.84/1.51  --res_out_proof                         true
% 7.84/1.51  
% 7.84/1.51  ------ Superposition Options
% 7.84/1.51  
% 7.84/1.51  --superposition_flag                    true
% 7.84/1.51  --sup_passive_queue_type                priority_queues
% 7.84/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.84/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.84/1.51  --demod_completeness_check              fast
% 7.84/1.51  --demod_use_ground                      true
% 7.84/1.51  --sup_to_prop_solver                    passive
% 7.84/1.51  --sup_prop_simpl_new                    true
% 7.84/1.51  --sup_prop_simpl_given                  true
% 7.84/1.51  --sup_fun_splitting                     true
% 7.84/1.51  --sup_smt_interval                      50000
% 7.84/1.51  
% 7.84/1.51  ------ Superposition Simplification Setup
% 7.84/1.51  
% 7.84/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.84/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.84/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.84/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.84/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.84/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.84/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.84/1.51  --sup_immed_triv                        [TrivRules]
% 7.84/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.51  --sup_immed_bw_main                     []
% 7.84/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.84/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.84/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.51  --sup_input_bw                          []
% 7.84/1.51  
% 7.84/1.51  ------ Combination Options
% 7.84/1.51  
% 7.84/1.51  --comb_res_mult                         3
% 7.84/1.51  --comb_sup_mult                         2
% 7.84/1.51  --comb_inst_mult                        10
% 7.84/1.51  
% 7.84/1.51  ------ Debug Options
% 7.84/1.51  
% 7.84/1.51  --dbg_backtrace                         false
% 7.84/1.51  --dbg_dump_prop_clauses                 false
% 7.84/1.51  --dbg_dump_prop_clauses_file            -
% 7.84/1.51  --dbg_out_stat                          false
% 7.84/1.51  ------ Parsing...
% 7.84/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.84/1.51  
% 7.84/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.84/1.51  
% 7.84/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.84/1.51  
% 7.84/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.84/1.51  ------ Proving...
% 7.84/1.51  ------ Problem Properties 
% 7.84/1.51  
% 7.84/1.51  
% 7.84/1.51  clauses                                 68
% 7.84/1.51  conjectures                             4
% 7.84/1.51  EPR                                     3
% 7.84/1.51  Horn                                    47
% 7.84/1.51  unary                                   11
% 7.84/1.51  binary                                  28
% 7.84/1.51  lits                                    170
% 7.84/1.51  lits eq                                 49
% 7.84/1.51  fd_pure                                 0
% 7.84/1.51  fd_pseudo                               0
% 7.84/1.51  fd_cond                                 3
% 7.84/1.51  fd_pseudo_cond                          5
% 7.84/1.51  AC symbols                              0
% 7.84/1.51  
% 7.84/1.51  ------ Schedule dynamic 5 is on 
% 7.84/1.51  
% 7.84/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.84/1.51  
% 7.84/1.51  
% 7.84/1.51  ------ 
% 7.84/1.51  Current options:
% 7.84/1.51  ------ 
% 7.84/1.51  
% 7.84/1.51  ------ Input Options
% 7.84/1.51  
% 7.84/1.51  --out_options                           all
% 7.84/1.51  --tptp_safe_out                         true
% 7.84/1.51  --problem_path                          ""
% 7.84/1.51  --include_path                          ""
% 7.84/1.51  --clausifier                            res/vclausify_rel
% 7.84/1.51  --clausifier_options                    ""
% 7.84/1.51  --stdin                                 false
% 7.84/1.51  --stats_out                             all
% 7.84/1.51  
% 7.84/1.51  ------ General Options
% 7.84/1.51  
% 7.84/1.51  --fof                                   false
% 7.84/1.51  --time_out_real                         305.
% 7.84/1.51  --time_out_virtual                      -1.
% 7.84/1.51  --symbol_type_check                     false
% 7.84/1.51  --clausify_out                          false
% 7.84/1.51  --sig_cnt_out                           false
% 7.84/1.51  --trig_cnt_out                          false
% 7.84/1.51  --trig_cnt_out_tolerance                1.
% 7.84/1.51  --trig_cnt_out_sk_spl                   false
% 7.84/1.51  --abstr_cl_out                          false
% 7.84/1.51  
% 7.84/1.51  ------ Global Options
% 7.84/1.51  
% 7.84/1.51  --schedule                              default
% 7.84/1.51  --add_important_lit                     false
% 7.84/1.51  --prop_solver_per_cl                    1000
% 7.84/1.51  --min_unsat_core                        false
% 7.84/1.51  --soft_assumptions                      false
% 7.84/1.51  --soft_lemma_size                       3
% 7.84/1.51  --prop_impl_unit_size                   0
% 7.84/1.51  --prop_impl_unit                        []
% 7.84/1.51  --share_sel_clauses                     true
% 7.84/1.51  --reset_solvers                         false
% 7.84/1.51  --bc_imp_inh                            [conj_cone]
% 7.84/1.51  --conj_cone_tolerance                   3.
% 7.84/1.51  --extra_neg_conj                        none
% 7.84/1.51  --large_theory_mode                     true
% 7.84/1.51  --prolific_symb_bound                   200
% 7.84/1.51  --lt_threshold                          2000
% 7.84/1.51  --clause_weak_htbl                      true
% 7.84/1.51  --gc_record_bc_elim                     false
% 7.84/1.51  
% 7.84/1.51  ------ Preprocessing Options
% 7.84/1.51  
% 7.84/1.51  --preprocessing_flag                    true
% 7.84/1.51  --time_out_prep_mult                    0.1
% 7.84/1.51  --splitting_mode                        input
% 7.84/1.51  --splitting_grd                         true
% 7.84/1.51  --splitting_cvd                         false
% 7.84/1.51  --splitting_cvd_svl                     false
% 7.84/1.51  --splitting_nvd                         32
% 7.84/1.51  --sub_typing                            true
% 7.84/1.51  --prep_gs_sim                           true
% 7.84/1.51  --prep_unflatten                        true
% 7.84/1.51  --prep_res_sim                          true
% 7.84/1.51  --prep_upred                            true
% 7.84/1.51  --prep_sem_filter                       exhaustive
% 7.84/1.51  --prep_sem_filter_out                   false
% 7.84/1.51  --pred_elim                             true
% 7.84/1.51  --res_sim_input                         true
% 7.84/1.51  --eq_ax_congr_red                       true
% 7.84/1.51  --pure_diseq_elim                       true
% 7.84/1.51  --brand_transform                       false
% 7.84/1.51  --non_eq_to_eq                          false
% 7.84/1.51  --prep_def_merge                        true
% 7.84/1.51  --prep_def_merge_prop_impl              false
% 7.84/1.51  --prep_def_merge_mbd                    true
% 7.84/1.51  --prep_def_merge_tr_red                 false
% 7.84/1.51  --prep_def_merge_tr_cl                  false
% 7.84/1.51  --smt_preprocessing                     true
% 7.84/1.51  --smt_ac_axioms                         fast
% 7.84/1.51  --preprocessed_out                      false
% 7.84/1.51  --preprocessed_stats                    false
% 7.84/1.51  
% 7.84/1.51  ------ Abstraction refinement Options
% 7.84/1.51  
% 7.84/1.51  --abstr_ref                             []
% 7.84/1.51  --abstr_ref_prep                        false
% 7.84/1.51  --abstr_ref_until_sat                   false
% 7.84/1.51  --abstr_ref_sig_restrict                funpre
% 7.84/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.84/1.51  --abstr_ref_under                       []
% 7.84/1.51  
% 7.84/1.51  ------ SAT Options
% 7.84/1.51  
% 7.84/1.51  --sat_mode                              false
% 7.84/1.51  --sat_fm_restart_options                ""
% 7.84/1.51  --sat_gr_def                            false
% 7.84/1.51  --sat_epr_types                         true
% 7.84/1.51  --sat_non_cyclic_types                  false
% 7.84/1.51  --sat_finite_models                     false
% 7.84/1.51  --sat_fm_lemmas                         false
% 7.84/1.51  --sat_fm_prep                           false
% 7.84/1.51  --sat_fm_uc_incr                        true
% 7.84/1.51  --sat_out_model                         small
% 7.84/1.51  --sat_out_clauses                       false
% 7.84/1.51  
% 7.84/1.51  ------ QBF Options
% 7.84/1.51  
% 7.84/1.51  --qbf_mode                              false
% 7.84/1.51  --qbf_elim_univ                         false
% 7.84/1.51  --qbf_dom_inst                          none
% 7.84/1.51  --qbf_dom_pre_inst                      false
% 7.84/1.51  --qbf_sk_in                             false
% 7.84/1.51  --qbf_pred_elim                         true
% 7.84/1.51  --qbf_split                             512
% 7.84/1.51  
% 7.84/1.51  ------ BMC1 Options
% 7.84/1.51  
% 7.84/1.51  --bmc1_incremental                      false
% 7.84/1.51  --bmc1_axioms                           reachable_all
% 7.84/1.51  --bmc1_min_bound                        0
% 7.84/1.51  --bmc1_max_bound                        -1
% 7.84/1.51  --bmc1_max_bound_default                -1
% 7.84/1.51  --bmc1_symbol_reachability              true
% 7.84/1.51  --bmc1_property_lemmas                  false
% 7.84/1.51  --bmc1_k_induction                      false
% 7.84/1.51  --bmc1_non_equiv_states                 false
% 7.84/1.51  --bmc1_deadlock                         false
% 7.84/1.51  --bmc1_ucm                              false
% 7.84/1.51  --bmc1_add_unsat_core                   none
% 7.84/1.51  --bmc1_unsat_core_children              false
% 7.84/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.84/1.51  --bmc1_out_stat                         full
% 7.84/1.51  --bmc1_ground_init                      false
% 7.84/1.51  --bmc1_pre_inst_next_state              false
% 7.84/1.51  --bmc1_pre_inst_state                   false
% 7.84/1.51  --bmc1_pre_inst_reach_state             false
% 7.84/1.51  --bmc1_out_unsat_core                   false
% 7.84/1.51  --bmc1_aig_witness_out                  false
% 7.84/1.51  --bmc1_verbose                          false
% 7.84/1.51  --bmc1_dump_clauses_tptp                false
% 7.84/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.84/1.51  --bmc1_dump_file                        -
% 7.84/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.84/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.84/1.51  --bmc1_ucm_extend_mode                  1
% 7.84/1.51  --bmc1_ucm_init_mode                    2
% 7.84/1.51  --bmc1_ucm_cone_mode                    none
% 7.84/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.84/1.51  --bmc1_ucm_relax_model                  4
% 7.84/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.84/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.84/1.51  --bmc1_ucm_layered_model                none
% 7.84/1.51  --bmc1_ucm_max_lemma_size               10
% 7.84/1.51  
% 7.84/1.51  ------ AIG Options
% 7.84/1.51  
% 7.84/1.51  --aig_mode                              false
% 7.84/1.51  
% 7.84/1.51  ------ Instantiation Options
% 7.84/1.51  
% 7.84/1.51  --instantiation_flag                    true
% 7.84/1.51  --inst_sos_flag                         true
% 7.84/1.51  --inst_sos_phase                        true
% 7.84/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.84/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.84/1.51  --inst_lit_sel_side                     none
% 7.84/1.51  --inst_solver_per_active                1400
% 7.84/1.51  --inst_solver_calls_frac                1.
% 7.84/1.51  --inst_passive_queue_type               priority_queues
% 7.84/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.84/1.51  --inst_passive_queues_freq              [25;2]
% 7.84/1.51  --inst_dismatching                      true
% 7.84/1.51  --inst_eager_unprocessed_to_passive     true
% 7.84/1.51  --inst_prop_sim_given                   true
% 7.84/1.51  --inst_prop_sim_new                     false
% 7.84/1.51  --inst_subs_new                         false
% 7.84/1.51  --inst_eq_res_simp                      false
% 7.84/1.51  --inst_subs_given                       false
% 7.84/1.51  --inst_orphan_elimination               true
% 7.84/1.51  --inst_learning_loop_flag               true
% 7.84/1.51  --inst_learning_start                   3000
% 7.84/1.51  --inst_learning_factor                  2
% 7.84/1.51  --inst_start_prop_sim_after_learn       3
% 7.84/1.51  --inst_sel_renew                        solver
% 7.84/1.51  --inst_lit_activity_flag                true
% 7.84/1.51  --inst_restr_to_given                   false
% 7.84/1.51  --inst_activity_threshold               500
% 7.84/1.51  --inst_out_proof                        true
% 7.84/1.51  
% 7.84/1.51  ------ Resolution Options
% 7.84/1.51  
% 7.84/1.51  --resolution_flag                       false
% 7.84/1.51  --res_lit_sel                           adaptive
% 7.84/1.51  --res_lit_sel_side                      none
% 7.84/1.51  --res_ordering                          kbo
% 7.84/1.51  --res_to_prop_solver                    active
% 7.84/1.51  --res_prop_simpl_new                    false
% 7.84/1.51  --res_prop_simpl_given                  true
% 7.84/1.51  --res_passive_queue_type                priority_queues
% 7.84/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.84/1.51  --res_passive_queues_freq               [15;5]
% 7.84/1.51  --res_forward_subs                      full
% 7.84/1.51  --res_backward_subs                     full
% 7.84/1.51  --res_forward_subs_resolution           true
% 7.84/1.51  --res_backward_subs_resolution          true
% 7.84/1.51  --res_orphan_elimination                true
% 7.84/1.51  --res_time_limit                        2.
% 7.84/1.51  --res_out_proof                         true
% 7.84/1.51  
% 7.84/1.51  ------ Superposition Options
% 7.84/1.51  
% 7.84/1.51  --superposition_flag                    true
% 7.84/1.51  --sup_passive_queue_type                priority_queues
% 7.84/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.84/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.84/1.51  --demod_completeness_check              fast
% 7.84/1.51  --demod_use_ground                      true
% 7.84/1.51  --sup_to_prop_solver                    passive
% 7.84/1.51  --sup_prop_simpl_new                    true
% 7.84/1.51  --sup_prop_simpl_given                  true
% 7.84/1.51  --sup_fun_splitting                     true
% 7.84/1.51  --sup_smt_interval                      50000
% 7.84/1.51  
% 7.84/1.51  ------ Superposition Simplification Setup
% 7.84/1.51  
% 7.84/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.84/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.84/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.84/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.84/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.84/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.84/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.84/1.51  --sup_immed_triv                        [TrivRules]
% 7.84/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.51  --sup_immed_bw_main                     []
% 7.84/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.84/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.84/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.51  --sup_input_bw                          []
% 7.84/1.51  
% 7.84/1.51  ------ Combination Options
% 7.84/1.51  
% 7.84/1.51  --comb_res_mult                         3
% 7.84/1.51  --comb_sup_mult                         2
% 7.84/1.51  --comb_inst_mult                        10
% 7.84/1.51  
% 7.84/1.51  ------ Debug Options
% 7.84/1.51  
% 7.84/1.51  --dbg_backtrace                         false
% 7.84/1.51  --dbg_dump_prop_clauses                 false
% 7.84/1.51  --dbg_dump_prop_clauses_file            -
% 7.84/1.51  --dbg_out_stat                          false
% 7.84/1.51  
% 7.84/1.51  
% 7.84/1.51  
% 7.84/1.51  
% 7.84/1.51  ------ Proving...
% 7.84/1.51  
% 7.84/1.51  
% 7.84/1.51  % SZS status Theorem for theBenchmark.p
% 7.84/1.51  
% 7.84/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.84/1.51  
% 7.84/1.51  fof(f29,axiom,(
% 7.84/1.51    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 7.84/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.51  
% 7.84/1.51  fof(f66,plain,(
% 7.84/1.51    ! [X1,X0,X2] : (sP2(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 7.84/1.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 7.84/1.51  
% 7.84/1.51  fof(f67,plain,(
% 7.84/1.51    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP2(X1,X0,X2))),
% 7.84/1.51    inference(definition_folding,[],[f29,f66])).
% 7.84/1.51  
% 7.84/1.51  fof(f95,plain,(
% 7.84/1.51    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP2(X1,X0,X2)) & (sP2(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 7.84/1.51    inference(nnf_transformation,[],[f67])).
% 7.84/1.51  
% 7.84/1.51  fof(f169,plain,(
% 7.84/1.51    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 7.84/1.51    inference(cnf_transformation,[],[f95])).
% 7.84/1.51  
% 7.84/1.51  fof(f193,plain,(
% 7.84/1.51    ( ! [X0,X1] : (sP2(X1,X0,k1_funct_2(X0,X1))) )),
% 7.84/1.51    inference(equality_resolution,[],[f169])).
% 7.84/1.51  
% 7.84/1.51  fof(f30,conjecture,(
% 7.84/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 7.84/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.51  
% 7.84/1.51  fof(f31,negated_conjecture,(
% 7.84/1.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 7.84/1.51    inference(negated_conjecture,[],[f30])).
% 7.84/1.51  
% 7.84/1.51  fof(f61,plain,(
% 7.84/1.51    ? [X0,X1,X2] : ((~r2_hidden(X2,k1_funct_2(X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.84/1.51    inference(ennf_transformation,[],[f31])).
% 7.84/1.51  
% 7.84/1.51  fof(f62,plain,(
% 7.84/1.51    ? [X0,X1,X2] : (~r2_hidden(X2,k1_funct_2(X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.84/1.51    inference(flattening,[],[f61])).
% 7.84/1.51  
% 7.84/1.51  fof(f96,plain,(
% 7.84/1.51    ? [X0,X1,X2] : (~r2_hidden(X2,k1_funct_2(X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (~r2_hidden(sK15,k1_funct_2(sK13,sK14)) & (k1_xboole_0 = sK13 | k1_xboole_0 != sK14) & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) & v1_funct_2(sK15,sK13,sK14) & v1_funct_1(sK15))),
% 7.84/1.51    introduced(choice_axiom,[])).
% 7.84/1.51  
% 7.84/1.51  fof(f97,plain,(
% 7.84/1.51    ~r2_hidden(sK15,k1_funct_2(sK13,sK14)) & (k1_xboole_0 = sK13 | k1_xboole_0 != sK14) & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) & v1_funct_2(sK15,sK13,sK14) & v1_funct_1(sK15)),
% 7.84/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f62,f96])).
% 7.84/1.51  
% 7.84/1.51  fof(f173,plain,(
% 7.84/1.51    m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))),
% 7.84/1.51    inference(cnf_transformation,[],[f97])).
% 7.84/1.51  
% 7.84/1.51  fof(f25,axiom,(
% 7.84/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.84/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.51  
% 7.84/1.51  fof(f54,plain,(
% 7.84/1.51    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.84/1.51    inference(ennf_transformation,[],[f25])).
% 7.84/1.51  
% 7.84/1.51  fof(f146,plain,(
% 7.84/1.51    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.84/1.51    inference(cnf_transformation,[],[f54])).
% 7.84/1.51  
% 7.84/1.51  fof(f23,axiom,(
% 7.84/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 7.84/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.51  
% 7.84/1.51  fof(f52,plain,(
% 7.84/1.51    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.84/1.51    inference(ennf_transformation,[],[f23])).
% 7.84/1.51  
% 7.84/1.51  fof(f144,plain,(
% 7.84/1.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.84/1.51    inference(cnf_transformation,[],[f52])).
% 7.84/1.51  
% 7.84/1.51  fof(f10,axiom,(
% 7.84/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.84/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.51  
% 7.84/1.51  fof(f76,plain,(
% 7.84/1.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.84/1.51    inference(nnf_transformation,[],[f10])).
% 7.84/1.51  
% 7.84/1.51  fof(f113,plain,(
% 7.84/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.84/1.51    inference(cnf_transformation,[],[f76])).
% 7.84/1.51  
% 7.84/1.51  fof(f28,axiom,(
% 7.84/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.84/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.51  
% 7.84/1.51  fof(f59,plain,(
% 7.84/1.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.84/1.51    inference(ennf_transformation,[],[f28])).
% 7.84/1.51  
% 7.84/1.51  fof(f60,plain,(
% 7.84/1.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.84/1.51    inference(flattening,[],[f59])).
% 7.84/1.51  
% 7.84/1.51  fof(f88,plain,(
% 7.84/1.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.84/1.51    inference(nnf_transformation,[],[f60])).
% 7.84/1.51  
% 7.84/1.51  fof(f151,plain,(
% 7.84/1.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.84/1.51    inference(cnf_transformation,[],[f88])).
% 7.84/1.51  
% 7.84/1.51  fof(f172,plain,(
% 7.84/1.51    v1_funct_2(sK15,sK13,sK14)),
% 7.84/1.51    inference(cnf_transformation,[],[f97])).
% 7.84/1.51  
% 7.84/1.51  fof(f24,axiom,(
% 7.84/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.84/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.51  
% 7.84/1.51  fof(f53,plain,(
% 7.84/1.51    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.84/1.51    inference(ennf_transformation,[],[f24])).
% 7.84/1.51  
% 7.84/1.51  fof(f145,plain,(
% 7.84/1.51    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.84/1.51    inference(cnf_transformation,[],[f53])).
% 7.84/1.51  
% 7.84/1.51  fof(f89,plain,(
% 7.84/1.51    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 7.84/1.51    inference(nnf_transformation,[],[f66])).
% 7.84/1.51  
% 7.84/1.51  fof(f90,plain,(
% 7.84/1.51    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP2(X0,X1,X2)))),
% 7.84/1.51    inference(rectify,[],[f89])).
% 7.84/1.51  
% 7.84/1.51  fof(f93,plain,(
% 7.84/1.51    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK12(X0,X1,X6)),X0) & k1_relat_1(sK12(X0,X1,X6)) = X1 & sK12(X0,X1,X6) = X6 & v1_funct_1(sK12(X0,X1,X6)) & v1_relat_1(sK12(X0,X1,X6))))),
% 7.84/1.51    introduced(choice_axiom,[])).
% 7.84/1.51  
% 7.84/1.51  fof(f92,plain,(
% 7.84/1.51    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK11(X0,X1,X2)),X0) & k1_relat_1(sK11(X0,X1,X2)) = X1 & sK11(X0,X1,X2) = X3 & v1_funct_1(sK11(X0,X1,X2)) & v1_relat_1(sK11(X0,X1,X2))))) )),
% 7.84/1.51    introduced(choice_axiom,[])).
% 7.84/1.51  
% 7.84/1.51  fof(f91,plain,(
% 7.84/1.51    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK10(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK10(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 7.84/1.51    introduced(choice_axiom,[])).
% 7.84/1.51  
% 7.84/1.51  fof(f94,plain,(
% 7.84/1.51    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK10(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK10(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK11(X0,X1,X2)),X0) & k1_relat_1(sK11(X0,X1,X2)) = X1 & sK10(X0,X1,X2) = sK11(X0,X1,X2) & v1_funct_1(sK11(X0,X1,X2)) & v1_relat_1(sK11(X0,X1,X2))) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK12(X0,X1,X6)),X0) & k1_relat_1(sK12(X0,X1,X6)) = X1 & sK12(X0,X1,X6) = X6 & v1_funct_1(sK12(X0,X1,X6)) & v1_relat_1(sK12(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP2(X0,X1,X2)))),
% 7.84/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f90,f93,f92,f91])).
% 7.84/1.51  
% 7.84/1.51  fof(f162,plain,(
% 7.84/1.51    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7) | ~sP2(X0,X1,X2)) )),
% 7.84/1.51    inference(cnf_transformation,[],[f94])).
% 7.84/1.51  
% 7.84/1.51  fof(f191,plain,(
% 7.84/1.51    ( ! [X6,X2,X0,X7] : (r2_hidden(X6,X2) | ~r1_tarski(k2_relat_1(X7),X0) | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7) | ~sP2(X0,k1_relat_1(X7),X2)) )),
% 7.84/1.51    inference(equality_resolution,[],[f162])).
% 7.84/1.51  
% 7.84/1.51  fof(f192,plain,(
% 7.84/1.51    ( ! [X2,X0,X7] : (r2_hidden(X7,X2) | ~r1_tarski(k2_relat_1(X7),X0) | ~v1_funct_1(X7) | ~v1_relat_1(X7) | ~sP2(X0,k1_relat_1(X7),X2)) )),
% 7.84/1.51    inference(equality_resolution,[],[f191])).
% 7.84/1.51  
% 7.84/1.51  fof(f171,plain,(
% 7.84/1.51    v1_funct_1(sK15)),
% 7.84/1.51    inference(cnf_transformation,[],[f97])).
% 7.84/1.51  
% 7.84/1.51  fof(f20,axiom,(
% 7.84/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.84/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.51  
% 7.84/1.51  fof(f49,plain,(
% 7.84/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.84/1.51    inference(ennf_transformation,[],[f20])).
% 7.84/1.51  
% 7.84/1.51  fof(f141,plain,(
% 7.84/1.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.84/1.51    inference(cnf_transformation,[],[f49])).
% 7.84/1.51  
% 7.84/1.51  fof(f175,plain,(
% 7.84/1.51    ~r2_hidden(sK15,k1_funct_2(sK13,sK14))),
% 7.84/1.51    inference(cnf_transformation,[],[f97])).
% 7.84/1.51  
% 7.84/1.51  fof(f170,plain,(
% 7.84/1.51    ( ! [X2,X0,X1] : (k1_funct_2(X0,X1) = X2 | ~sP2(X1,X0,X2)) )),
% 7.84/1.51    inference(cnf_transformation,[],[f95])).
% 7.84/1.51  
% 7.84/1.51  fof(f2,axiom,(
% 7.84/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.84/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.51  
% 7.84/1.51  fof(f34,plain,(
% 7.84/1.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.84/1.51    inference(ennf_transformation,[],[f2])).
% 7.84/1.51  
% 7.84/1.51  fof(f99,plain,(
% 7.84/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.84/1.51    inference(cnf_transformation,[],[f34])).
% 7.84/1.51  
% 7.84/1.51  fof(f4,axiom,(
% 7.84/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.84/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.51  
% 7.84/1.51  fof(f101,plain,(
% 7.84/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.84/1.51    inference(cnf_transformation,[],[f4])).
% 7.84/1.51  
% 7.84/1.51  fof(f177,plain,(
% 7.84/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.84/1.51    inference(definition_unfolding,[],[f99,f101])).
% 7.84/1.51  
% 7.84/1.51  fof(f174,plain,(
% 7.84/1.51    k1_xboole_0 = sK13 | k1_xboole_0 != sK14),
% 7.84/1.51    inference(cnf_transformation,[],[f97])).
% 7.84/1.51  
% 7.84/1.51  fof(f3,axiom,(
% 7.84/1.51    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.84/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.51  
% 7.84/1.51  fof(f100,plain,(
% 7.84/1.51    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.84/1.51    inference(cnf_transformation,[],[f3])).
% 7.84/1.51  
% 7.84/1.51  fof(f178,plain,(
% 7.84/1.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.84/1.51    inference(definition_unfolding,[],[f100,f101])).
% 7.84/1.51  
% 7.84/1.51  fof(f7,axiom,(
% 7.84/1.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.84/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.51  
% 7.84/1.51  fof(f72,plain,(
% 7.84/1.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.84/1.51    inference(nnf_transformation,[],[f7])).
% 7.84/1.51  
% 7.84/1.51  fof(f73,plain,(
% 7.84/1.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.84/1.51    inference(flattening,[],[f72])).
% 7.84/1.51  
% 7.84/1.51  fof(f108,plain,(
% 7.84/1.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.84/1.51    inference(cnf_transformation,[],[f73])).
% 7.84/1.51  
% 7.84/1.51  fof(f184,plain,(
% 7.84/1.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.84/1.51    inference(equality_resolution,[],[f108])).
% 7.84/1.51  
% 7.84/1.51  fof(f15,axiom,(
% 7.84/1.51    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 7.84/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.51  
% 7.84/1.51  fof(f41,plain,(
% 7.84/1.51    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.84/1.51    inference(ennf_transformation,[],[f15])).
% 7.84/1.51  
% 7.84/1.51  fof(f77,plain,(
% 7.84/1.51    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.84/1.51    inference(nnf_transformation,[],[f41])).
% 7.84/1.51  
% 7.84/1.51  fof(f121,plain,(
% 7.84/1.51    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.84/1.51    inference(cnf_transformation,[],[f77])).
% 7.84/1.51  
% 7.84/1.51  fof(f107,plain,(
% 7.84/1.51    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.84/1.51    inference(cnf_transformation,[],[f73])).
% 7.84/1.51  
% 7.84/1.51  fof(f14,axiom,(
% 7.84/1.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.84/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.51  
% 7.84/1.51  fof(f119,plain,(
% 7.84/1.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 7.84/1.51    inference(cnf_transformation,[],[f14])).
% 7.84/1.51  
% 7.84/1.51  cnf(c_4434,plain,
% 7.84/1.51      ( ~ sP2(X0,X1,X2) | sP2(X0,X3,X4) | X3 != X1 | X4 != X2 ),
% 7.84/1.51      theory(equality) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_17634,plain,
% 7.84/1.51      ( ~ sP2(X0,X1,X2)
% 7.84/1.51      | sP2(X0,k1_relat_1(sK15),k1_funct_2(sK13,sK14))
% 7.84/1.51      | k1_funct_2(sK13,sK14) != X2
% 7.84/1.51      | k1_relat_1(sK15) != X1 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_4434]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_32712,plain,
% 7.84/1.51      ( ~ sP2(X0,X1,k1_funct_2(X2,X3))
% 7.84/1.51      | sP2(X0,k1_relat_1(sK15),k1_funct_2(sK13,sK14))
% 7.84/1.51      | k1_funct_2(sK13,sK14) != k1_funct_2(X2,X3)
% 7.84/1.51      | k1_relat_1(sK15) != X1 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_17634]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_32714,plain,
% 7.84/1.51      ( sP2(k1_xboole_0,k1_relat_1(sK15),k1_funct_2(sK13,sK14))
% 7.84/1.51      | ~ sP2(k1_xboole_0,k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))
% 7.84/1.51      | k1_funct_2(sK13,sK14) != k1_funct_2(k1_xboole_0,k1_xboole_0)
% 7.84/1.51      | k1_relat_1(sK15) != k1_xboole_0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_32712]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_4417,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_14443,plain,
% 7.84/1.51      ( X0 != X1 | X0 = k2_relat_1(X2) | k2_relat_1(X2) != X1 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_4417]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_14444,plain,
% 7.84/1.51      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 7.84/1.51      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 7.84/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_14443]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_70,plain,
% 7.84/1.51      ( sP2(X0,X1,k1_funct_2(X1,X0)) ),
% 7.84/1.51      inference(cnf_transformation,[],[f193]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5659,plain,
% 7.84/1.51      ( sP2(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 7.84/1.51      inference(predicate_to_equality,[status(thm)],[c_70]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_73,negated_conjecture,
% 7.84/1.51      ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) ),
% 7.84/1.51      inference(cnf_transformation,[],[f173]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5657,plain,
% 7.84/1.51      ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) = iProver_top ),
% 7.84/1.51      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_46,plain,
% 7.84/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.84/1.51      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.84/1.51      inference(cnf_transformation,[],[f146]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5677,plain,
% 7.84/1.51      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.84/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.84/1.51      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_9708,plain,
% 7.84/1.51      ( k2_relset_1(sK13,sK14,sK15) = k2_relat_1(sK15) ),
% 7.84/1.51      inference(superposition,[status(thm)],[c_5657,c_5677]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_44,plain,
% 7.84/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.84/1.51      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 7.84/1.51      inference(cnf_transformation,[],[f144]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5679,plain,
% 7.84/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.84/1.51      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 7.84/1.51      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_11506,plain,
% 7.84/1.51      ( m1_subset_1(k2_relat_1(sK15),k1_zfmisc_1(sK14)) = iProver_top
% 7.84/1.51      | m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) != iProver_top ),
% 7.84/1.51      inference(superposition,[status(thm)],[c_9708,c_5679]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_78,plain,
% 7.84/1.51      ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) = iProver_top ),
% 7.84/1.51      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_11658,plain,
% 7.84/1.51      ( m1_subset_1(k2_relat_1(sK15),k1_zfmisc_1(sK14)) = iProver_top ),
% 7.84/1.51      inference(global_propositional_subsumption,
% 7.84/1.51                [status(thm)],
% 7.84/1.51                [c_11506,c_78]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_14,plain,
% 7.84/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.84/1.51      inference(cnf_transformation,[],[f113]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5701,plain,
% 7.84/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.84/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.84/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_11662,plain,
% 7.84/1.51      ( r1_tarski(k2_relat_1(sK15),sK14) = iProver_top ),
% 7.84/1.51      inference(superposition,[status(thm)],[c_11658,c_5701]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_56,plain,
% 7.84/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.84/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.84/1.51      | k1_relset_1(X1,X2,X0) = X1
% 7.84/1.51      | k1_xboole_0 = X2 ),
% 7.84/1.51      inference(cnf_transformation,[],[f151]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_74,negated_conjecture,
% 7.84/1.51      ( v1_funct_2(sK15,sK13,sK14) ),
% 7.84/1.51      inference(cnf_transformation,[],[f172]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_994,plain,
% 7.84/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.84/1.51      | k1_relset_1(X1,X2,X0) = X1
% 7.84/1.51      | sK14 != X2
% 7.84/1.51      | sK13 != X1
% 7.84/1.51      | sK15 != X0
% 7.84/1.51      | k1_xboole_0 = X2 ),
% 7.84/1.51      inference(resolution_lifted,[status(thm)],[c_56,c_74]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_995,plain,
% 7.84/1.51      ( ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
% 7.84/1.51      | k1_relset_1(sK13,sK14,sK15) = sK13
% 7.84/1.51      | k1_xboole_0 = sK14 ),
% 7.84/1.51      inference(unflattening,[status(thm)],[c_994]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_997,plain,
% 7.84/1.51      ( k1_relset_1(sK13,sK14,sK15) = sK13 | k1_xboole_0 = sK14 ),
% 7.84/1.51      inference(global_propositional_subsumption,
% 7.84/1.51                [status(thm)],
% 7.84/1.51                [c_995,c_73]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_45,plain,
% 7.84/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.84/1.51      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.84/1.51      inference(cnf_transformation,[],[f145]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5678,plain,
% 7.84/1.51      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.84/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.84/1.51      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_10500,plain,
% 7.84/1.51      ( k1_relset_1(sK13,sK14,sK15) = k1_relat_1(sK15) ),
% 7.84/1.51      inference(superposition,[status(thm)],[c_5657,c_5678]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_11094,plain,
% 7.84/1.51      ( k1_relat_1(sK15) = sK13 | sK14 = k1_xboole_0 ),
% 7.84/1.51      inference(superposition,[status(thm)],[c_997,c_10500]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_63,plain,
% 7.84/1.51      ( ~ sP2(X0,k1_relat_1(X1),X2)
% 7.84/1.51      | r2_hidden(X1,X2)
% 7.84/1.51      | ~ r1_tarski(k2_relat_1(X1),X0)
% 7.84/1.51      | ~ v1_funct_1(X1)
% 7.84/1.51      | ~ v1_relat_1(X1) ),
% 7.84/1.51      inference(cnf_transformation,[],[f192]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5666,plain,
% 7.84/1.51      ( sP2(X0,k1_relat_1(X1),X2) != iProver_top
% 7.84/1.51      | r2_hidden(X1,X2) = iProver_top
% 7.84/1.51      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 7.84/1.51      | v1_funct_1(X1) != iProver_top
% 7.84/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.84/1.51      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_13013,plain,
% 7.84/1.51      ( sK14 = k1_xboole_0
% 7.84/1.51      | sP2(X0,sK13,X1) != iProver_top
% 7.84/1.51      | r2_hidden(sK15,X1) = iProver_top
% 7.84/1.51      | r1_tarski(k2_relat_1(sK15),X0) != iProver_top
% 7.84/1.51      | v1_funct_1(sK15) != iProver_top
% 7.84/1.51      | v1_relat_1(sK15) != iProver_top ),
% 7.84/1.51      inference(superposition,[status(thm)],[c_11094,c_5666]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_75,negated_conjecture,
% 7.84/1.51      ( v1_funct_1(sK15) ),
% 7.84/1.51      inference(cnf_transformation,[],[f171]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_76,plain,
% 7.84/1.51      ( v1_funct_1(sK15) = iProver_top ),
% 7.84/1.51      inference(predicate_to_equality,[status(thm)],[c_75]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_41,plain,
% 7.84/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.84/1.51      | v1_relat_1(X0) ),
% 7.84/1.51      inference(cnf_transformation,[],[f141]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5794,plain,
% 7.84/1.51      ( ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.84/1.51      | v1_relat_1(sK15) ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_41]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5840,plain,
% 7.84/1.51      ( ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
% 7.84/1.51      | v1_relat_1(sK15) ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_5794]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5841,plain,
% 7.84/1.51      ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) != iProver_top
% 7.84/1.51      | v1_relat_1(sK15) = iProver_top ),
% 7.84/1.51      inference(predicate_to_equality,[status(thm)],[c_5840]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_13679,plain,
% 7.84/1.51      ( sK14 = k1_xboole_0
% 7.84/1.51      | sP2(X0,sK13,X1) != iProver_top
% 7.84/1.51      | r2_hidden(sK15,X1) = iProver_top
% 7.84/1.51      | r1_tarski(k2_relat_1(sK15),X0) != iProver_top ),
% 7.84/1.51      inference(global_propositional_subsumption,
% 7.84/1.51                [status(thm)],
% 7.84/1.51                [c_13013,c_76,c_78,c_5841]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_13685,plain,
% 7.84/1.51      ( sK14 = k1_xboole_0
% 7.84/1.51      | sP2(sK14,sK13,X0) != iProver_top
% 7.84/1.51      | r2_hidden(sK15,X0) = iProver_top ),
% 7.84/1.51      inference(superposition,[status(thm)],[c_11662,c_13679]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_71,negated_conjecture,
% 7.84/1.51      ( ~ r2_hidden(sK15,k1_funct_2(sK13,sK14)) ),
% 7.84/1.51      inference(cnf_transformation,[],[f175]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_79,plain,
% 7.84/1.51      ( r2_hidden(sK15,k1_funct_2(sK13,sK14)) != iProver_top ),
% 7.84/1.51      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_4421,plain,
% 7.84/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.84/1.51      theory(equality) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5778,plain,
% 7.84/1.51      ( ~ r2_hidden(X0,X1)
% 7.84/1.51      | r2_hidden(sK15,k1_funct_2(sK13,sK14))
% 7.84/1.51      | k1_funct_2(sK13,sK14) != X1
% 7.84/1.51      | sK15 != X0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_4421]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5819,plain,
% 7.84/1.51      ( ~ r2_hidden(sK15,X0)
% 7.84/1.51      | r2_hidden(sK15,k1_funct_2(sK13,sK14))
% 7.84/1.51      | k1_funct_2(sK13,sK14) != X0
% 7.84/1.51      | sK15 != sK15 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_5778]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5820,plain,
% 7.84/1.51      ( k1_funct_2(sK13,sK14) != X0
% 7.84/1.51      | sK15 != sK15
% 7.84/1.51      | r2_hidden(sK15,X0) != iProver_top
% 7.84/1.51      | r2_hidden(sK15,k1_funct_2(sK13,sK14)) = iProver_top ),
% 7.84/1.51      inference(predicate_to_equality,[status(thm)],[c_5819]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_4416,plain,( X0 = X0 ),theory(equality) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5871,plain,
% 7.84/1.51      ( sK15 = sK15 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_4416]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_69,plain,
% 7.84/1.51      ( ~ sP2(X0,X1,X2) | k1_funct_2(X1,X0) = X2 ),
% 7.84/1.51      inference(cnf_transformation,[],[f170]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_7688,plain,
% 7.84/1.51      ( ~ sP2(sK14,sK13,X0) | k1_funct_2(sK13,sK14) = X0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_69]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_7689,plain,
% 7.84/1.51      ( k1_funct_2(sK13,sK14) = X0 | sP2(sK14,sK13,X0) != iProver_top ),
% 7.84/1.51      inference(predicate_to_equality,[status(thm)],[c_7688]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_13774,plain,
% 7.84/1.51      ( sP2(sK14,sK13,X0) != iProver_top | sK14 = k1_xboole_0 ),
% 7.84/1.51      inference(global_propositional_subsumption,
% 7.84/1.51                [status(thm)],
% 7.84/1.51                [c_13685,c_79,c_5820,c_5871,c_7689]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_13775,plain,
% 7.84/1.51      ( sK14 = k1_xboole_0 | sP2(sK14,sK13,X0) != iProver_top ),
% 7.84/1.51      inference(renaming,[status(thm)],[c_13774]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_13780,plain,
% 7.84/1.51      ( sK14 = k1_xboole_0 ),
% 7.84/1.51      inference(superposition,[status(thm)],[c_5659,c_13775]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_6991,plain,
% 7.84/1.51      ( r1_tarski(sK15,k2_zfmisc_1(sK13,sK14)) = iProver_top ),
% 7.84/1.51      inference(superposition,[status(thm)],[c_5657,c_5701]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_1,plain,
% 7.84/1.51      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.84/1.51      inference(cnf_transformation,[],[f177]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5707,plain,
% 7.84/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 7.84/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 7.84/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_8624,plain,
% 7.84/1.51      ( k4_xboole_0(sK15,k4_xboole_0(sK15,k2_zfmisc_1(sK13,sK14))) = sK15 ),
% 7.84/1.51      inference(superposition,[status(thm)],[c_6991,c_5707]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_13794,plain,
% 7.84/1.51      ( k4_xboole_0(sK15,k4_xboole_0(sK15,k2_zfmisc_1(sK13,k1_xboole_0))) = sK15 ),
% 7.84/1.51      inference(demodulation,[status(thm)],[c_13780,c_8624]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_72,negated_conjecture,
% 7.84/1.51      ( k1_xboole_0 != sK14 | k1_xboole_0 = sK13 ),
% 7.84/1.51      inference(cnf_transformation,[],[f174]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_13801,plain,
% 7.84/1.51      ( sK13 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.84/1.51      inference(demodulation,[status(thm)],[c_13780,c_72]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_13802,plain,
% 7.84/1.51      ( sK13 = k1_xboole_0 ),
% 7.84/1.51      inference(equality_resolution_simp,[status(thm)],[c_13801]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_13811,plain,
% 7.84/1.51      ( k4_xboole_0(sK15,k4_xboole_0(sK15,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = sK15 ),
% 7.84/1.51      inference(demodulation,[status(thm)],[c_13794,c_13802]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_2,plain,
% 7.84/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.84/1.51      inference(cnf_transformation,[],[f178]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_8,plain,
% 7.84/1.51      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.84/1.51      inference(cnf_transformation,[],[f184]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_13812,plain,
% 7.84/1.51      ( sK15 = k1_xboole_0 ),
% 7.84/1.51      inference(demodulation,[status(thm)],[c_13811,c_2,c_8]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_13459,plain,
% 7.84/1.51      ( X0 != X1 | X0 = k2_zfmisc_1(X2,X3) | k2_zfmisc_1(X2,X3) != X1 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_4417]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_13460,plain,
% 7.84/1.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.84/1.51      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 7.84/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_13459]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_4419,plain,
% 7.84/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.84/1.51      theory(equality) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_10519,plain,
% 7.84/1.51      ( r1_tarski(X0,X1)
% 7.84/1.51      | ~ r1_tarski(sK15,k2_zfmisc_1(X2,X3))
% 7.84/1.51      | X1 != k2_zfmisc_1(X2,X3)
% 7.84/1.51      | X0 != sK15 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_4419]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_10528,plain,
% 7.84/1.51      ( ~ r1_tarski(sK15,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 7.84/1.51      | r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.84/1.51      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 7.84/1.51      | k1_xboole_0 != sK15 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_10519]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_20,plain,
% 7.84/1.51      ( ~ v1_relat_1(X0)
% 7.84/1.51      | k1_relat_1(X0) = k1_xboole_0
% 7.84/1.51      | k2_relat_1(X0) != k1_xboole_0 ),
% 7.84/1.51      inference(cnf_transformation,[],[f121]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_9625,plain,
% 7.84/1.51      ( ~ v1_relat_1(sK15)
% 7.84/1.51      | k1_relat_1(sK15) = k1_xboole_0
% 7.84/1.51      | k2_relat_1(sK15) != k1_xboole_0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_20]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_4436,plain,
% 7.84/1.51      ( X0 != X1 | X2 != X3 | k1_funct_2(X0,X2) = k1_funct_2(X1,X3) ),
% 7.84/1.51      theory(equality) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_9168,plain,
% 7.84/1.51      ( k1_funct_2(sK13,sK14) = k1_funct_2(X0,X1)
% 7.84/1.51      | sK14 != X1
% 7.84/1.51      | sK13 != X0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_4436]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_9169,plain,
% 7.84/1.51      ( k1_funct_2(sK13,sK14) = k1_funct_2(k1_xboole_0,k1_xboole_0)
% 7.84/1.51      | sK14 != k1_xboole_0
% 7.84/1.51      | sK13 != k1_xboole_0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_9168]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_8659,plain,
% 7.84/1.51      ( sK14 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK14 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_4417]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_8660,plain,
% 7.84/1.51      ( sK14 != k1_xboole_0
% 7.84/1.51      | k1_xboole_0 = sK14
% 7.84/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_8659]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_6072,plain,
% 7.84/1.51      ( ~ r1_tarski(X0,X1)
% 7.84/1.51      | r1_tarski(sK15,k2_zfmisc_1(X2,X3))
% 7.84/1.51      | k2_zfmisc_1(X2,X3) != X1
% 7.84/1.51      | sK15 != X0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_4419]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_6525,plain,
% 7.84/1.51      ( ~ r1_tarski(sK15,X0)
% 7.84/1.51      | r1_tarski(sK15,k2_zfmisc_1(X1,X2))
% 7.84/1.51      | k2_zfmisc_1(X1,X2) != X0
% 7.84/1.51      | sK15 != sK15 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_6072]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_7133,plain,
% 7.84/1.51      ( r1_tarski(sK15,k2_zfmisc_1(X0,X1))
% 7.84/1.51      | ~ r1_tarski(sK15,k2_zfmisc_1(sK13,sK14))
% 7.84/1.51      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK13,sK14)
% 7.84/1.51      | sK15 != sK15 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_6525]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_7135,plain,
% 7.84/1.51      ( ~ r1_tarski(sK15,k2_zfmisc_1(sK13,sK14))
% 7.84/1.51      | r1_tarski(sK15,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 7.84/1.51      | k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK13,sK14)
% 7.84/1.51      | sK15 != sK15 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_7133]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_4427,plain,
% 7.84/1.51      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 7.84/1.51      theory(equality) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_7046,plain,
% 7.84/1.51      ( k2_relat_1(sK15) = k2_relat_1(X0) | sK15 != X0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_4427]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_7047,plain,
% 7.84/1.51      ( k2_relat_1(sK15) = k2_relat_1(k1_xboole_0)
% 7.84/1.51      | sK15 != k1_xboole_0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_7046]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_6259,plain,
% 7.84/1.51      ( X0 != X1 | k2_relat_1(sK15) != X1 | k2_relat_1(sK15) = X0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_4417]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_7012,plain,
% 7.84/1.51      ( X0 != k2_relat_1(X1)
% 7.84/1.51      | k2_relat_1(sK15) = X0
% 7.84/1.51      | k2_relat_1(sK15) != k2_relat_1(X1) ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_6259]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_7013,plain,
% 7.84/1.51      ( k2_relat_1(sK15) != k2_relat_1(k1_xboole_0)
% 7.84/1.51      | k2_relat_1(sK15) = k1_xboole_0
% 7.84/1.51      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_7012]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_4422,plain,
% 7.84/1.51      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 7.84/1.51      theory(equality) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_6708,plain,
% 7.84/1.51      ( X0 != sK14
% 7.84/1.51      | X1 != sK13
% 7.84/1.51      | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK13,sK14) ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_4422]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_6709,plain,
% 7.84/1.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK13,sK14)
% 7.84/1.51      | k1_xboole_0 != sK14
% 7.84/1.51      | k1_xboole_0 != sK13 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_6708]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_6063,plain,
% 7.84/1.51      ( ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.84/1.51      | r1_tarski(sK15,k2_zfmisc_1(X0,X1)) ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_14]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_6467,plain,
% 7.84/1.51      ( ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
% 7.84/1.51      | r1_tarski(sK15,k2_zfmisc_1(sK13,sK14)) ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_6063]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_6056,plain,
% 7.84/1.51      ( X0 != X1 | X0 = sK15 | sK15 != X1 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_4417]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_6057,plain,
% 7.84/1.51      ( sK15 != k1_xboole_0
% 7.84/1.51      | k1_xboole_0 = sK15
% 7.84/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_6056]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5977,plain,
% 7.84/1.51      ( sK13 = sK13 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_4416]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5947,plain,
% 7.84/1.51      ( ~ r1_tarski(X0,X1)
% 7.84/1.51      | r1_tarski(k2_relat_1(sK15),X2)
% 7.84/1.51      | X2 != X1
% 7.84/1.51      | k2_relat_1(sK15) != X0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_4419]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5949,plain,
% 7.84/1.51      ( r1_tarski(k2_relat_1(sK15),k1_xboole_0)
% 7.84/1.51      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.84/1.51      | k2_relat_1(sK15) != k1_xboole_0
% 7.84/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_5947]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5793,plain,
% 7.84/1.51      ( sK13 != X0 | sK13 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_4417]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5838,plain,
% 7.84/1.51      ( sK13 != sK13 | sK13 = k1_xboole_0 | k1_xboole_0 != sK13 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_5793]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5773,plain,
% 7.84/1.51      ( ~ sP2(X0,k1_relat_1(sK15),k1_funct_2(sK13,sK14))
% 7.84/1.51      | r2_hidden(sK15,k1_funct_2(sK13,sK14))
% 7.84/1.51      | ~ r1_tarski(k2_relat_1(sK15),X0)
% 7.84/1.51      | ~ v1_funct_1(sK15)
% 7.84/1.51      | ~ v1_relat_1(sK15) ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_63]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_5775,plain,
% 7.84/1.51      ( ~ sP2(k1_xboole_0,k1_relat_1(sK15),k1_funct_2(sK13,sK14))
% 7.84/1.51      | r2_hidden(sK15,k1_funct_2(sK13,sK14))
% 7.84/1.51      | ~ r1_tarski(k2_relat_1(sK15),k1_xboole_0)
% 7.84/1.51      | ~ v1_funct_1(sK15)
% 7.84/1.51      | ~ v1_relat_1(sK15) ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_5773]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_252,plain,
% 7.84/1.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_8]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_9,plain,
% 7.84/1.51      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.84/1.51      | k1_xboole_0 = X1
% 7.84/1.51      | k1_xboole_0 = X0 ),
% 7.84/1.51      inference(cnf_transformation,[],[f107]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_251,plain,
% 7.84/1.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.84/1.51      | k1_xboole_0 = k1_xboole_0 ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_18,plain,
% 7.84/1.51      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.84/1.51      inference(cnf_transformation,[],[f119]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(c_81,plain,
% 7.84/1.51      ( sP2(k1_xboole_0,k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
% 7.84/1.51      inference(instantiation,[status(thm)],[c_70]) ).
% 7.84/1.51  
% 7.84/1.51  cnf(contradiction,plain,
% 7.84/1.51      ( $false ),
% 7.84/1.51      inference(minisat,
% 7.84/1.51                [status(thm)],
% 7.84/1.51                [c_32714,c_14444,c_13812,c_13780,c_13460,c_10528,c_9625,
% 7.84/1.51                 c_9169,c_8660,c_7135,c_7047,c_7013,c_6709,c_6467,c_6057,
% 7.84/1.51                 c_5977,c_5949,c_5871,c_5840,c_5838,c_5775,c_252,c_251,
% 7.84/1.51                 c_18,c_81,c_71,c_72,c_73,c_75]) ).
% 7.84/1.51  
% 7.84/1.51  
% 7.84/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.84/1.51  
% 7.84/1.51  ------                               Statistics
% 7.84/1.51  
% 7.84/1.51  ------ General
% 7.84/1.51  
% 7.84/1.51  abstr_ref_over_cycles:                  0
% 7.84/1.51  abstr_ref_under_cycles:                 0
% 7.84/1.51  gc_basic_clause_elim:                   0
% 7.84/1.51  forced_gc_time:                         0
% 7.84/1.51  parsing_time:                           0.025
% 7.84/1.51  unif_index_cands_time:                  0.
% 7.84/1.51  unif_index_add_time:                    0.
% 7.84/1.51  orderings_time:                         0.
% 7.84/1.51  out_proof_time:                         0.016
% 7.84/1.51  total_time:                             0.91
% 7.84/1.51  num_of_symbols:                         72
% 7.84/1.51  num_of_terms:                           33492
% 7.84/1.51  
% 7.84/1.51  ------ Preprocessing
% 7.84/1.51  
% 7.84/1.51  num_of_splits:                          0
% 7.84/1.51  num_of_split_atoms:                     0
% 7.84/1.51  num_of_reused_defs:                     0
% 7.84/1.51  num_eq_ax_congr_red:                    96
% 7.84/1.51  num_of_sem_filtered_clauses:            1
% 7.84/1.51  num_of_subtypes:                        0
% 7.84/1.51  monotx_restored_types:                  0
% 7.84/1.51  sat_num_of_epr_types:                   0
% 7.84/1.51  sat_num_of_non_cyclic_types:            0
% 7.84/1.51  sat_guarded_non_collapsed_types:        0
% 7.84/1.51  num_pure_diseq_elim:                    0
% 7.84/1.51  simp_replaced_by:                       0
% 7.84/1.51  res_preprocessed:                       323
% 7.84/1.51  prep_upred:                             0
% 7.84/1.51  prep_unflattend:                        153
% 7.84/1.51  smt_new_axioms:                         0
% 7.84/1.51  pred_elim_cands:                        7
% 7.84/1.51  pred_elim:                              4
% 7.84/1.51  pred_elim_cl:                           8
% 7.84/1.51  pred_elim_cycles:                       8
% 7.84/1.51  merged_defs:                            16
% 7.84/1.51  merged_defs_ncl:                        0
% 7.84/1.51  bin_hyper_res:                          19
% 7.84/1.51  prep_cycles:                            4
% 7.84/1.51  pred_elim_time:                         0.051
% 7.84/1.51  splitting_time:                         0.
% 7.84/1.51  sem_filter_time:                        0.
% 7.84/1.51  monotx_time:                            0.
% 7.84/1.51  subtype_inf_time:                       0.
% 7.84/1.51  
% 7.84/1.51  ------ Problem properties
% 7.84/1.51  
% 7.84/1.51  clauses:                                68
% 7.84/1.51  conjectures:                            4
% 7.84/1.51  epr:                                    3
% 7.84/1.51  horn:                                   47
% 7.84/1.51  ground:                                 9
% 7.84/1.51  unary:                                  11
% 7.84/1.51  binary:                                 28
% 7.84/1.51  lits:                                   170
% 7.84/1.51  lits_eq:                                49
% 7.84/1.51  fd_pure:                                0
% 7.84/1.51  fd_pseudo:                              0
% 7.84/1.51  fd_cond:                                3
% 7.84/1.51  fd_pseudo_cond:                         5
% 7.84/1.51  ac_symbols:                             0
% 7.84/1.51  
% 7.84/1.51  ------ Propositional Solver
% 7.84/1.51  
% 7.84/1.51  prop_solver_calls:                      32
% 7.84/1.51  prop_fast_solver_calls:                 2887
% 7.84/1.51  smt_solver_calls:                       0
% 7.84/1.51  smt_fast_solver_calls:                  0
% 7.84/1.51  prop_num_of_clauses:                    13388
% 7.84/1.51  prop_preprocess_simplified:             29578
% 7.84/1.51  prop_fo_subsumed:                       14
% 7.84/1.51  prop_solver_time:                       0.
% 7.84/1.51  smt_solver_time:                        0.
% 7.84/1.51  smt_fast_solver_time:                   0.
% 7.84/1.51  prop_fast_solver_time:                  0.
% 7.84/1.51  prop_unsat_core_time:                   0.001
% 7.84/1.51  
% 7.84/1.51  ------ QBF
% 7.84/1.51  
% 7.84/1.51  qbf_q_res:                              0
% 7.84/1.51  qbf_num_tautologies:                    0
% 7.84/1.51  qbf_prep_cycles:                        0
% 7.84/1.51  
% 7.84/1.51  ------ BMC1
% 7.84/1.51  
% 7.84/1.51  bmc1_current_bound:                     -1
% 7.84/1.51  bmc1_last_solved_bound:                 -1
% 7.84/1.51  bmc1_unsat_core_size:                   -1
% 7.84/1.51  bmc1_unsat_core_parents_size:           -1
% 7.84/1.51  bmc1_merge_next_fun:                    0
% 7.84/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.84/1.51  
% 7.84/1.51  ------ Instantiation
% 7.84/1.51  
% 7.84/1.51  inst_num_of_clauses:                    2866
% 7.84/1.51  inst_num_in_passive:                    1798
% 7.84/1.51  inst_num_in_active:                     1053
% 7.84/1.51  inst_num_in_unprocessed:                14
% 7.84/1.51  inst_num_of_loops:                      1376
% 7.84/1.51  inst_num_of_learning_restarts:          0
% 7.84/1.51  inst_num_moves_active_passive:          319
% 7.84/1.51  inst_lit_activity:                      0
% 7.84/1.51  inst_lit_activity_moves:                0
% 7.84/1.51  inst_num_tautologies:                   0
% 7.84/1.51  inst_num_prop_implied:                  0
% 7.84/1.51  inst_num_existing_simplified:           0
% 7.84/1.51  inst_num_eq_res_simplified:             0
% 7.84/1.51  inst_num_child_elim:                    0
% 7.84/1.51  inst_num_of_dismatching_blockings:      2605
% 7.84/1.51  inst_num_of_non_proper_insts:           3828
% 7.84/1.51  inst_num_of_duplicates:                 0
% 7.84/1.51  inst_inst_num_from_inst_to_res:         0
% 7.84/1.51  inst_dismatching_checking_time:         0.
% 7.84/1.51  
% 7.84/1.51  ------ Resolution
% 7.84/1.51  
% 7.84/1.51  res_num_of_clauses:                     0
% 7.84/1.51  res_num_in_passive:                     0
% 7.84/1.51  res_num_in_active:                      0
% 7.84/1.51  res_num_of_loops:                       327
% 7.84/1.51  res_forward_subset_subsumed:            314
% 7.84/1.51  res_backward_subset_subsumed:           0
% 7.84/1.51  res_forward_subsumed:                   0
% 7.84/1.51  res_backward_subsumed:                  0
% 7.84/1.51  res_forward_subsumption_resolution:     0
% 7.84/1.51  res_backward_subsumption_resolution:    0
% 7.84/1.51  res_clause_to_clause_subsumption:       4045
% 7.84/1.51  res_orphan_elimination:                 0
% 7.84/1.51  res_tautology_del:                      128
% 7.84/1.51  res_num_eq_res_simplified:              0
% 7.84/1.51  res_num_sel_changes:                    0
% 7.84/1.51  res_moves_from_active_to_pass:          0
% 7.84/1.51  
% 7.84/1.51  ------ Superposition
% 7.84/1.51  
% 7.84/1.51  sup_time_total:                         0.
% 7.84/1.51  sup_time_generating:                    0.
% 7.84/1.51  sup_time_sim_full:                      0.
% 7.84/1.51  sup_time_sim_immed:                     0.
% 7.84/1.51  
% 7.84/1.51  sup_num_of_clauses:                     1095
% 7.84/1.51  sup_num_in_active:                      222
% 7.84/1.51  sup_num_in_passive:                     873
% 7.84/1.51  sup_num_of_loops:                       274
% 7.84/1.51  sup_fw_superposition:                   1069
% 7.84/1.51  sup_bw_superposition:                   418
% 7.84/1.51  sup_immediate_simplified:               412
% 7.84/1.51  sup_given_eliminated:                   0
% 7.84/1.51  comparisons_done:                       0
% 7.84/1.51  comparisons_avoided:                    31
% 7.84/1.51  
% 7.84/1.51  ------ Simplifications
% 7.84/1.51  
% 7.84/1.51  
% 7.84/1.51  sim_fw_subset_subsumed:                 39
% 7.84/1.51  sim_bw_subset_subsumed:                 10
% 7.84/1.51  sim_fw_subsumed:                        58
% 7.84/1.51  sim_bw_subsumed:                        35
% 7.84/1.51  sim_fw_subsumption_res:                 0
% 7.84/1.51  sim_bw_subsumption_res:                 0
% 7.84/1.51  sim_tautology_del:                      10
% 7.84/1.51  sim_eq_tautology_del:                   63
% 7.84/1.51  sim_eq_res_simp:                        4
% 7.84/1.51  sim_fw_demodulated:                     259
% 7.84/1.51  sim_bw_demodulated:                     40
% 7.84/1.51  sim_light_normalised:                   40
% 7.84/1.51  sim_joinable_taut:                      0
% 7.84/1.51  sim_joinable_simp:                      0
% 7.84/1.51  sim_ac_normalised:                      0
% 7.84/1.51  sim_smt_subsumption:                    0
% 7.84/1.51  
%------------------------------------------------------------------------------

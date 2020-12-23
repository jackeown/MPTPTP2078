%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0839+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:53 EST 2020

% Result     : Theorem 3.73s
% Output     : Refutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 162 expanded)
%              Number of leaves         :   18 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  230 ( 765 expanded)
%              Number of equality atoms :   46 ( 158 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5201,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5200,f4040])).

fof(f4040,plain,(
    k1_xboole_0 != k1_relat_1(sK115) ),
    inference(subsumption_resolution,[],[f4039,f4009])).

fof(f4009,plain,(
    v1_relat_1(sK115) ),
    inference(resolution,[],[f2602,f2828])).

fof(f2828,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1381])).

fof(f1381,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f2602,plain,(
    m1_subset_1(sK115,k1_zfmisc_1(k2_zfmisc_1(sK114,sK113))) ),
    inference(cnf_transformation,[],[f2078])).

fof(f2078,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK114,sK113,sK115))
        | ~ m1_subset_1(X3,sK114) )
    & k1_xboole_0 != k2_relset_1(sK114,sK113,sK115)
    & m1_subset_1(sK115,k1_zfmisc_1(k2_zfmisc_1(sK114,sK113)))
    & ~ v1_xboole_0(sK114)
    & ~ v1_xboole_0(sK113) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK113,sK114,sK115])],[f1272,f2077,f2076,f2075])).

fof(f2075,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k2_relset_1(X1,X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,sK113,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,sK113,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK113))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK113) ) ),
    introduced(choice_axiom,[])).

fof(f2076,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k1_relset_1(X1,sK113,X2))
                | ~ m1_subset_1(X3,X1) )
            & k1_xboole_0 != k2_relset_1(X1,sK113,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK113))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k1_relset_1(sK114,sK113,X2))
              | ~ m1_subset_1(X3,sK114) )
          & k1_xboole_0 != k2_relset_1(sK114,sK113,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK114,sK113))) )
      & ~ v1_xboole_0(sK114) ) ),
    introduced(choice_axiom,[])).

fof(f2077,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(sK114,sK113,X2))
            | ~ m1_subset_1(X3,sK114) )
        & k1_xboole_0 != k2_relset_1(sK114,sK113,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK114,sK113))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(sK114,sK113,sK115))
          | ~ m1_subset_1(X3,sK114) )
      & k1_xboole_0 != k2_relset_1(sK114,sK113,sK115)
      & m1_subset_1(sK115,k1_zfmisc_1(k2_zfmisc_1(sK114,sK113))) ) ),
    introduced(choice_axiom,[])).

fof(f1272,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1271])).

fof(f1271,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1261])).

fof(f1261,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1260])).

fof(f1260,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

fof(f4039,plain,
    ( k1_xboole_0 != k1_relat_1(sK115)
    | ~ v1_relat_1(sK115) ),
    inference(trivial_inequality_removal,[],[f4038])).

fof(f4038,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK115)
    | ~ v1_relat_1(sK115) ),
    inference(superposition,[],[f4034,f2718])).

fof(f2718,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2147])).

fof(f2147,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1329])).

fof(f1329,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f860])).

fof(f860,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f4034,plain,(
    k1_xboole_0 != k2_relat_1(sK115) ),
    inference(subsumption_resolution,[],[f4032,f2602])).

fof(f4032,plain,
    ( k1_xboole_0 != k2_relat_1(sK115)
    | ~ m1_subset_1(sK115,k1_zfmisc_1(k2_zfmisc_1(sK114,sK113))) ),
    inference(superposition,[],[f2603,f2647])).

fof(f2647,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1296])).

fof(f1296,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1225])).

fof(f1225,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f2603,plain,(
    k1_xboole_0 != k2_relset_1(sK114,sK113,sK115) ),
    inference(cnf_transformation,[],[f2078])).

fof(f5200,plain,(
    k1_xboole_0 = k1_relat_1(sK115) ),
    inference(subsumption_resolution,[],[f5135,f4230])).

fof(f4230,plain,(
    ~ r2_hidden(sK130(k1_relat_1(sK115)),sK114) ),
    inference(resolution,[],[f4226,f2751])).

fof(f2751,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1346])).

fof(f1346,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f4226,plain,(
    ~ m1_subset_1(sK130(k1_relat_1(sK115)),sK114) ),
    inference(subsumption_resolution,[],[f4168,f4040])).

fof(f4168,plain,
    ( ~ m1_subset_1(sK130(k1_relat_1(sK115)),sK114)
    | k1_xboole_0 = k1_relat_1(sK115) ),
    inference(resolution,[],[f4116,f2699])).

fof(f2699,plain,(
    ! [X0] :
      ( r2_hidden(sK130(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2136])).

fof(f2136,plain,(
    ! [X0] :
      ( r2_hidden(sK130(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK130])],[f1319,f2135])).

fof(f2135,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK130(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1319,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f4116,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK115))
      | ~ m1_subset_1(X0,sK114) ) ),
    inference(subsumption_resolution,[],[f4114,f2602])).

fof(f4114,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK115))
      | ~ m1_subset_1(X0,sK114)
      | ~ m1_subset_1(sK115,k1_zfmisc_1(k2_zfmisc_1(sK114,sK113))) ) ),
    inference(superposition,[],[f2604,f2631])).

fof(f2631,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1290])).

fof(f1290,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1224])).

fof(f1224,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f2604,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK114,sK113,sK115))
      | ~ m1_subset_1(X3,sK114) ) ),
    inference(cnf_transformation,[],[f2078])).

fof(f5135,plain,
    ( r2_hidden(sK130(k1_relat_1(sK115)),sK114)
    | k1_xboole_0 = k1_relat_1(sK115) ),
    inference(resolution,[],[f5109,f2699])).

fof(f5109,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK115))
      | r2_hidden(X0,sK114) ) ),
    inference(resolution,[],[f4462,f3953])).

fof(f3953,plain,(
    ! [X0] : sP39(X0,k1_relat_1(X0)) ),
    inference(equality_resolution,[],[f3002])).

fof(f3002,plain,(
    ! [X0,X1] :
      ( sP39(X0,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2285])).

fof(f2285,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ~ sP39(X0,X1) )
      & ( sP39(X0,X1)
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1965])).

fof(f1965,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> sP39(X0,X1) ) ),
    inference(definition_folding,[],[f656,f1964])).

fof(f1964,plain,(
    ! [X0,X1] :
      ( sP39(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP39])])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f4462,plain,(
    ! [X17,X16] :
      ( ~ sP39(sK115,X17)
      | ~ r2_hidden(X16,X17)
      | r2_hidden(X16,sK114) ) ),
    inference(resolution,[],[f4262,f2998])).

fof(f2998,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK172(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | ~ sP39(X0,X1) ) ),
    inference(cnf_transformation,[],[f2284])).

fof(f2284,plain,(
    ! [X0,X1] :
      ( ( sP39(X0,X1)
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK170(X0,X1),X3),X0)
            | ~ r2_hidden(sK170(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK170(X0,X1),sK171(X0,X1)),X0)
            | r2_hidden(sK170(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK172(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP39(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK170,sK171,sK172])],[f2280,f2283,f2282,f2281])).

fof(f2281,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK170(X0,X1),X3),X0)
          | ~ r2_hidden(sK170(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK170(X0,X1),X4),X0)
          | r2_hidden(sK170(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2282,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK170(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK170(X0,X1),sK171(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f2283,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK172(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f2280,plain,(
    ! [X0,X1] :
      ( ( sP39(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP39(X0,X1) ) ) ),
    inference(rectify,[],[f2279])).

fof(f2279,plain,(
    ! [X0,X1] :
      ( ( sP39(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP39(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1964])).

fof(f4262,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(k4_tarski(X17,X18),sK115)
      | r2_hidden(X17,sK114) ) ),
    inference(resolution,[],[f4014,f2794])).

fof(f2794,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2198])).

fof(f2198,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f2197])).

fof(f2197,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f325])).

fof(f325,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f4014,plain,(
    ! [X5] :
      ( r2_hidden(X5,k2_zfmisc_1(sK114,sK113))
      | ~ r2_hidden(X5,sK115) ) ),
    inference(resolution,[],[f2602,f2747])).

fof(f2747,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f1342])).

fof(f1342,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f488])).

fof(f488,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
%------------------------------------------------------------------------------

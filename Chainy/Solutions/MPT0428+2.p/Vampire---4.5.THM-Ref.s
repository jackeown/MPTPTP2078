%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0428+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:29 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 142 expanded)
%              Number of leaves         :   12 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  170 ( 478 expanded)
%              Number of equality atoms :   39 ( 141 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2503,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2499,f2373])).

fof(f2373,plain,(
    m1_setfam_1(sK42,sK41) ),
    inference(subsumption_resolution,[],[f2372,f1989])).

fof(f1989,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1435])).

fof(f1435,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1091])).

fof(f1091,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1090])).

fof(f1090,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2372,plain,
    ( m1_setfam_1(sK42,sK41)
    | ~ r1_tarski(sK41,sK41) ),
    inference(factoring,[],[f2091])).

fof(f2091,plain,(
    ! [X1] :
      ( m1_setfam_1(sK42,sK41)
      | m1_setfam_1(sK42,X1)
      | ~ r1_tarski(X1,sK41) ) ),
    inference(superposition,[],[f1223,f2028])).

fof(f2028,plain,
    ( sK41 = k3_tarski(sK42)
    | m1_setfam_1(sK42,sK41) ),
    inference(subsumption_resolution,[],[f2024,f1215])).

fof(f1215,plain,(
    m1_subset_1(sK42,k1_zfmisc_1(k1_zfmisc_1(sK41))) ),
    inference(cnf_transformation,[],[f975])).

fof(f975,plain,
    ( ( sK41 != k5_setfam_1(sK41,sK42)
      | ~ m1_setfam_1(sK42,sK41) )
    & ( sK41 = k5_setfam_1(sK41,sK42)
      | m1_setfam_1(sK42,sK41) )
    & m1_subset_1(sK42,k1_zfmisc_1(k1_zfmisc_1(sK41))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK41,sK42])],[f973,f974])).

fof(f974,plain,
    ( ? [X0,X1] :
        ( ( k5_setfam_1(X0,X1) != X0
          | ~ m1_setfam_1(X1,X0) )
        & ( k5_setfam_1(X0,X1) = X0
          | m1_setfam_1(X1,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( sK41 != k5_setfam_1(sK41,sK42)
        | ~ m1_setfam_1(sK42,sK41) )
      & ( sK41 = k5_setfam_1(sK41,sK42)
        | m1_setfam_1(sK42,sK41) )
      & m1_subset_1(sK42,k1_zfmisc_1(k1_zfmisc_1(sK41))) ) ),
    introduced(choice_axiom,[])).

fof(f973,plain,(
    ? [X0,X1] :
      ( ( k5_setfam_1(X0,X1) != X0
        | ~ m1_setfam_1(X1,X0) )
      & ( k5_setfam_1(X0,X1) = X0
        | m1_setfam_1(X1,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f972])).

fof(f972,plain,(
    ? [X0,X1] :
      ( ( k5_setfam_1(X0,X1) != X0
        | ~ m1_setfam_1(X1,X0) )
      & ( k5_setfam_1(X0,X1) = X0
        | m1_setfam_1(X1,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f631])).

fof(f631,plain,(
    ? [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <~> k5_setfam_1(X0,X1) = X0 )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f622])).

fof(f622,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( m1_setfam_1(X1,X0)
        <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    inference(negated_conjecture,[],[f621])).

fof(f621,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

fof(f2024,plain,
    ( sK41 = k3_tarski(sK42)
    | m1_setfam_1(sK42,sK41)
    | ~ m1_subset_1(sK42,k1_zfmisc_1(k1_zfmisc_1(sK41))) ),
    inference(superposition,[],[f1216,f1221])).

fof(f1221,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f637])).

fof(f637,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f572])).

fof(f572,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f1216,plain,
    ( sK41 = k5_setfam_1(sK41,sK42)
    | m1_setfam_1(sK42,sK41) ),
    inference(cnf_transformation,[],[f975])).

fof(f1223,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(X1))
      | m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f976])).

fof(f976,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f547])).

fof(f547,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f2499,plain,(
    ~ m1_setfam_1(sK42,sK41) ),
    inference(resolution,[],[f2496,f1222])).

fof(f1222,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f976])).

fof(f2496,plain,(
    ~ r1_tarski(sK41,k3_tarski(sK42)) ),
    inference(subsumption_resolution,[],[f2492,f2376])).

fof(f2376,plain,(
    sK41 != k3_tarski(sK42) ),
    inference(resolution,[],[f2374,f1986])).

fof(f1986,plain,(
    ! [X0] : sP12(X0,k3_tarski(X0)) ),
    inference(equality_resolution,[],[f1385])).

fof(f1385,plain,(
    ! [X0,X1] :
      ( sP12(X0,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1060])).

fof(f1060,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ~ sP12(X0,X1) )
      & ( sP12(X0,X1)
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f924])).

fof(f924,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> sP12(X0,X1) ) ),
    inference(definition_folding,[],[f287,f923,f922])).

fof(f922,plain,(
    ! [X0,X2] :
      ( sP11(X0,X2)
    <=> ? [X3] :
          ( r2_hidden(X3,X0)
          & r2_hidden(X2,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP11])])).

fof(f923,plain,(
    ! [X0,X1] :
      ( sP12(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP11(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP12])])).

fof(f287,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f2374,plain,(
    ! [X0] :
      ( ~ sP12(sK42,X0)
      | sK41 != X0 ) ),
    inference(subsumption_resolution,[],[f2131,f2373])).

fof(f2131,plain,(
    ! [X0] :
      ( sK41 != X0
      | ~ m1_setfam_1(sK42,sK41)
      | ~ sP12(sK42,X0) ) ),
    inference(superposition,[],[f2048,f1386])).

fof(f1386,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | ~ sP12(X0,X1) ) ),
    inference(cnf_transformation,[],[f1060])).

fof(f2048,plain,
    ( sK41 != k3_tarski(sK42)
    | ~ m1_setfam_1(sK42,sK41) ),
    inference(subsumption_resolution,[],[f2047,f1215])).

fof(f2047,plain,
    ( sK41 != k3_tarski(sK42)
    | ~ m1_setfam_1(sK42,sK41)
    | ~ m1_subset_1(sK42,k1_zfmisc_1(k1_zfmisc_1(sK41))) ),
    inference(superposition,[],[f1217,f1221])).

fof(f1217,plain,
    ( sK41 != k5_setfam_1(sK41,sK42)
    | ~ m1_setfam_1(sK42,sK41) ),
    inference(cnf_transformation,[],[f975])).

fof(f2492,plain,
    ( sK41 = k3_tarski(sK42)
    | ~ r1_tarski(sK41,k3_tarski(sK42)) ),
    inference(resolution,[],[f2490,f1437])).

fof(f1437,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1091])).

fof(f2490,plain,(
    r1_tarski(k3_tarski(sK42),sK41) ),
    inference(duplicate_literal_removal,[],[f2489])).

fof(f2489,plain,
    ( r1_tarski(k3_tarski(sK42),sK41)
    | r1_tarski(k3_tarski(sK42),sK41) ),
    inference(resolution,[],[f2069,f1396])).

fof(f1396,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK64(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f1070])).

fof(f1070,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK64(X0,X1),X1)
        & r2_hidden(sK64(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK64])],[f711,f1069])).

fof(f1069,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK64(X0,X1),X1)
        & r2_hidden(sK64(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f711,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f443])).

fof(f443,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f2069,plain,(
    ! [X19] :
      ( ~ r2_hidden(sK64(X19,sK41),sK42)
      | r1_tarski(k3_tarski(X19),sK41) ) ),
    inference(resolution,[],[f2053,f1397])).

fof(f1397,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK64(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f1070])).

fof(f2053,plain,(
    ! [X5] :
      ( r1_tarski(X5,sK41)
      | ~ r2_hidden(X5,sK42) ) ),
    inference(resolution,[],[f2021,f1226])).

fof(f1226,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f979])).

fof(f979,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f600])).

fof(f600,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f2021,plain,(
    ! [X5] :
      ( m1_subset_1(X5,k1_zfmisc_1(sK41))
      | ~ r2_hidden(X5,sK42) ) ),
    inference(resolution,[],[f1215,f1225])).

fof(f1225,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f639])).

fof(f639,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f638])).

fof(f638,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
%------------------------------------------------------------------------------

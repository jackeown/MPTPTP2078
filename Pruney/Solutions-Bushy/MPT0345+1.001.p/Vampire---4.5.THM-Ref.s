%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0345+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:47 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 347 expanded)
%              Number of leaves         :   19 ( 117 expanded)
%              Depth                    :   19
%              Number of atoms          :  453 (1677 expanded)
%              Number of equality atoms :   32 ( 154 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1520,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f713,f1082,f1511,f1519])).

fof(f1519,plain,
    ( ~ spl11_7
    | ~ spl11_8
    | spl11_16 ),
    inference(avatar_contradiction_clause,[],[f1518])).

fof(f1518,plain,
    ( $false
    | ~ spl11_7
    | ~ spl11_8
    | spl11_16 ),
    inference(subsumption_resolution,[],[f1517,f701])).

fof(f701,plain,
    ( m1_subset_1(k2_xboole_0(sK7,sK8),k1_zfmisc_1(sK5))
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f700])).

fof(f700,plain,
    ( spl11_7
  <=> m1_subset_1(k2_xboole_0(sK7,sK8),k1_zfmisc_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f1517,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK7,sK8),k1_zfmisc_1(sK5))
    | ~ spl11_8
    | spl11_16 ),
    inference(subsumption_resolution,[],[f1516,f53])).

fof(f53,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK6 != k4_subset_1(sK5,sK7,sK8)
    & ! [X4] :
        ( sP1(sK7,X4,sK8,sK6)
        | ~ m1_subset_1(X4,sK5) )
    & m1_subset_1(sK8,k1_zfmisc_1(sK5))
    & m1_subset_1(sK7,k1_zfmisc_1(sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f19,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k4_subset_1(X0,X2,X3) != X1
                & ! [X4] :
                    ( sP1(X2,X4,X3,X1)
                    | ~ m1_subset_1(X4,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( sK6 != k4_subset_1(sK5,X2,X3)
              & ! [X4] :
                  ( sP1(X2,X4,X3,sK6)
                  | ~ m1_subset_1(X4,sK5) )
              & m1_subset_1(X3,k1_zfmisc_1(sK5)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK5)) )
      & m1_subset_1(sK6,k1_zfmisc_1(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( sK6 != k4_subset_1(sK5,X2,X3)
            & ! [X4] :
                ( sP1(X2,X4,X3,sK6)
                | ~ m1_subset_1(X4,sK5) )
            & m1_subset_1(X3,k1_zfmisc_1(sK5)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK5)) )
   => ( ? [X3] :
          ( sK6 != k4_subset_1(sK5,sK7,X3)
          & ! [X4] :
              ( sP1(sK7,X4,X3,sK6)
              | ~ m1_subset_1(X4,sK5) )
          & m1_subset_1(X3,k1_zfmisc_1(sK5)) )
      & m1_subset_1(sK7,k1_zfmisc_1(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( sK6 != k4_subset_1(sK5,sK7,X3)
        & ! [X4] :
            ( sP1(sK7,X4,X3,sK6)
            | ~ m1_subset_1(X4,sK5) )
        & m1_subset_1(X3,k1_zfmisc_1(sK5)) )
   => ( sK6 != k4_subset_1(sK5,sK7,sK8)
      & ! [X4] :
          ( sP1(sK7,X4,sK8,sK6)
          | ~ m1_subset_1(X4,sK5) )
      & m1_subset_1(sK8,k1_zfmisc_1(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( sP1(X2,X4,X3,X1)
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_folding,[],[f10,f18,f17])).

fof(f17,plain,(
    ! [X3,X4,X2] :
      ( sP0(X3,X4,X2)
    <=> ( r2_hidden(X4,X3)
        | r2_hidden(X4,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X2,X4,X3,X1] :
      ( ( r2_hidden(X4,X1)
      <=> sP0(X3,X4,X2) )
      | ~ sP1(X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,X1)
                      <=> ( r2_hidden(X4,X3)
                          | r2_hidden(X4,X2) ) ) )
                 => k4_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ( r2_hidden(X4,X1)
                    <=> ( r2_hidden(X4,X3)
                        | r2_hidden(X4,X2) ) ) )
               => k4_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_subset_1)).

fof(f1516,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
    | ~ m1_subset_1(k2_xboole_0(sK7,sK8),k1_zfmisc_1(sK5))
    | ~ spl11_8
    | spl11_16 ),
    inference(subsumption_resolution,[],[f1513,f728])).

fof(f728,plain,
    ( ~ r1_tarski(k2_xboole_0(sK7,sK8),sK6)
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f725,f198])).

fof(f198,plain,(
    sK6 != k2_xboole_0(sK7,sK8) ),
    inference(subsumption_resolution,[],[f197,f54])).

fof(f54,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f33])).

fof(f197,plain,
    ( sK6 != k2_xboole_0(sK7,sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(sK5)) ),
    inference(subsumption_resolution,[],[f194,f55])).

fof(f55,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f33])).

fof(f194,plain,
    ( sK6 != k2_xboole_0(sK7,sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(sK5)) ),
    inference(superposition,[],[f57,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f57,plain,(
    sK6 != k4_subset_1(sK5,sK7,sK8) ),
    inference(cnf_transformation,[],[f33])).

fof(f725,plain,
    ( sK6 = k2_xboole_0(sK7,sK8)
    | ~ r1_tarski(k2_xboole_0(sK7,sK8),sK6)
    | ~ spl11_8 ),
    inference(resolution,[],[f706,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f706,plain,
    ( r1_tarski(sK6,k2_xboole_0(sK7,sK8))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f704])).

fof(f704,plain,
    ( spl11_8
  <=> r1_tarski(sK6,k2_xboole_0(sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f1513,plain,
    ( r1_tarski(k2_xboole_0(sK7,sK8),sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK5))
    | ~ m1_subset_1(k2_xboole_0(sK7,sK8),k1_zfmisc_1(sK5))
    | spl11_16 ),
    inference(resolution,[],[f1501,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X1,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | sP2(X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_folding,[],[f12,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f1501,plain,
    ( ~ sP2(sK6,k2_xboole_0(sK7,sK8),sK5)
    | spl11_16 ),
    inference(avatar_component_clause,[],[f1499])).

fof(f1499,plain,
    ( spl11_16
  <=> sP2(sK6,k2_xboole_0(sK7,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f1511,plain,(
    ~ spl11_16 ),
    inference(avatar_split_clause,[],[f1482,f1499])).

fof(f1482,plain,(
    ~ sP2(sK6,k2_xboole_0(sK7,sK8),sK5) ),
    inference(duplicate_literal_removal,[],[f1464])).

fof(f1464,plain,
    ( ~ sP2(sK6,k2_xboole_0(sK7,sK8),sK5)
    | ~ sP2(sK6,k2_xboole_0(sK7,sK8),sK5) ),
    inference(resolution,[],[f1380,f172])).

fof(f172,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK9(sK6,X0,sK5),sK7)
      | ~ sP2(sK6,X0,sK5) ) ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK9(sK6,X0,sK5),sK7)
      | ~ sP2(sK6,X0,sK5)
      | ~ sP2(sK6,X0,sK5) ) ),
    inference(resolution,[],[f149,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1,X2),X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(sK9(X0,X1,X2),X0)
        & r2_hidden(sK9(X0,X1,X2),X1)
        & m1_subset_1(sK9(X0,X1,X2),X2) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X2) )
     => ( ~ r2_hidden(sK9(X0,X1,X2),X0)
        & r2_hidden(sK9(X0,X1,X2),X1)
        & m1_subset_1(sK9(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X2) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f149,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1,sK5),sK6)
      | ~ r2_hidden(sK9(X0,X1,sK5),sK7)
      | ~ sP2(X0,X1,sK5) ) ),
    inference(resolution,[],[f146,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f146,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK5)
      | r2_hidden(X2,sK6)
      | ~ r2_hidden(X2,sK7) ) ),
    inference(resolution,[],[f143,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r2_hidden(X1,X0)
          & ~ r2_hidden(X1,X2) ) )
      & ( r2_hidden(X1,X0)
        | r2_hidden(X1,X2)
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X3,X4,X2] :
      ( ( sP0(X3,X4,X2)
        | ( ~ r2_hidden(X4,X3)
          & ~ r2_hidden(X4,X2) ) )
      & ( r2_hidden(X4,X3)
        | r2_hidden(X4,X2)
        | ~ sP0(X3,X4,X2) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X3,X4,X2] :
      ( ( sP0(X3,X4,X2)
        | ( ~ r2_hidden(X4,X3)
          & ~ r2_hidden(X4,X2) ) )
      & ( r2_hidden(X4,X3)
        | r2_hidden(X4,X2)
        | ~ sP0(X3,X4,X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f143,plain,(
    ! [X0] :
      ( ~ sP0(sK8,X0,sK7)
      | r2_hidden(X0,sK6)
      | ~ m1_subset_1(X0,sK5) ) ),
    inference(resolution,[],[f49,f56])).

fof(f56,plain,(
    ! [X4] :
      ( sP1(sK7,X4,sK8,sK6)
      | ~ m1_subset_1(X4,sK5) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ sP0(X2,X1,X0)
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X1,X3)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X1,X3) ) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X2,X4,X3,X1] :
      ( ( ( r2_hidden(X4,X1)
          | ~ sP0(X3,X4,X2) )
        & ( sP0(X3,X4,X2)
          | ~ r2_hidden(X4,X1) ) )
      | ~ sP1(X2,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f1380,plain,(
    ! [X28] :
      ( r2_hidden(sK9(sK6,k2_xboole_0(X28,sK8),sK5),X28)
      | ~ sP2(sK6,k2_xboole_0(X28,sK8),sK5) ) ),
    inference(duplicate_literal_removal,[],[f1370])).

fof(f1370,plain,(
    ! [X28] :
      ( r2_hidden(sK9(sK6,k2_xboole_0(X28,sK8),sK5),X28)
      | ~ sP2(sK6,k2_xboole_0(X28,sK8),sK5)
      | ~ sP2(sK6,k2_xboole_0(X28,sK8),sK5) ) ),
    inference(resolution,[],[f227,f151])).

fof(f151,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK9(sK6,X0,sK5),sK8)
      | ~ sP2(sK6,X0,sK5) ) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK9(sK6,X0,sK5),sK8)
      | ~ sP2(sK6,X0,sK5)
      | ~ sP2(sK6,X0,sK5) ) ),
    inference(resolution,[],[f148,f61])).

fof(f148,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1,sK5),sK6)
      | ~ r2_hidden(sK9(X0,X1,sK5),sK8)
      | ~ sP2(X0,X1,sK5) ) ),
    inference(resolution,[],[f145,f59])).

fof(f145,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK5)
      | r2_hidden(X1,sK6)
      | ~ r2_hidden(X1,sK8) ) ),
    inference(resolution,[],[f143,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f227,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK9(X0,k2_xboole_0(X1,X2),X3),X2)
      | r2_hidden(sK9(X0,k2_xboole_0(X1,X2),X3),X1)
      | ~ sP2(X0,k2_xboole_0(X1,X2),X3) ) ),
    inference(resolution,[],[f113,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ~ r2_hidden(X1,X0)
          & ~ r2_hidden(X1,X2) ) )
      & ( r2_hidden(X1,X0)
        | r2_hidden(X1,X2)
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X1,X3,X0] :
      ( ( sP3(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP3(X1,X3,X0) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X1,X3,X0] :
      ( ( sP3(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP3(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X1,X3,X0] :
      ( sP3(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,sK9(X1,k2_xboole_0(X2,X0),X3),X2)
      | ~ sP2(X1,k2_xboole_0(X2,X0),X3) ) ),
    inference(resolution,[],[f107,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X1)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,X2))
      | sP3(X2,X0,X1) ) ),
    inference(resolution,[],[f68,f79])).

fof(f79,plain,(
    ! [X0,X1] : sP4(X0,X1,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X1,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP4(X0,X1,X2) )
      & ( sP4(X0,X1,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP4(X0,X1,X2) ) ),
    inference(definition_folding,[],[f3,f23,f22])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP3(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP3(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ( ~ sP3(X1,sK10(X0,X1,X2),X0)
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( sP3(X1,sK10(X0,X1,X2),X0)
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP3(X1,X4,X0) )
            & ( sP3(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP3(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP3(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP3(X1,sK10(X0,X1,X2),X0)
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( sP3(X1,sK10(X0,X1,X2),X0)
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP3(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP3(X1,X4,X0) )
            & ( sP3(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP3(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP3(X1,X3,X0) )
            & ( sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f1082,plain,
    ( ~ spl11_7
    | spl11_8 ),
    inference(avatar_split_clause,[],[f1081,f704,f700])).

fof(f1081,plain,
    ( r1_tarski(sK6,k2_xboole_0(sK7,sK8))
    | ~ m1_subset_1(k2_xboole_0(sK7,sK8),k1_zfmisc_1(sK5)) ),
    inference(subsumption_resolution,[],[f1078,f53])).

fof(f1078,plain,
    ( r1_tarski(sK6,k2_xboole_0(sK7,sK8))
    | ~ m1_subset_1(k2_xboole_0(sK7,sK8),k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(resolution,[],[f692,f62])).

fof(f692,plain,(
    ~ sP2(k2_xboole_0(sK7,sK8),sK6,sK5) ),
    inference(duplicate_literal_removal,[],[f689])).

fof(f689,plain,
    ( ~ sP2(k2_xboole_0(sK7,sK8),sK6,sK5)
    | ~ sP2(k2_xboole_0(sK7,sK8),sK6,sK5) ),
    inference(resolution,[],[f683,f60])).

fof(f683,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK9(k2_xboole_0(sK7,sK8),X7,sK5),sK6)
      | ~ sP2(k2_xboole_0(sK7,sK8),X7,sK5) ) ),
    inference(duplicate_literal_removal,[],[f677])).

fof(f677,plain,(
    ! [X7] :
      ( ~ sP2(k2_xboole_0(sK7,sK8),X7,sK5)
      | ~ r2_hidden(sK9(k2_xboole_0(sK7,sK8),X7,sK5),sK6)
      | ~ sP2(k2_xboole_0(sK7,sK8),X7,sK5) ) ),
    inference(resolution,[],[f253,f235])).

fof(f235,plain,(
    ! [X14,X12,X13,X11] :
      ( ~ r2_hidden(sK9(k2_xboole_0(X11,X12),X13,X14),X11)
      | ~ sP2(k2_xboole_0(X11,X12),X13,X14) ) ),
    inference(resolution,[],[f118,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X0,sK9(k2_xboole_0(X1,X0),X2,X3),X1)
      | ~ sP2(k2_xboole_0(X1,X0),X2,X3) ) ),
    inference(resolution,[],[f110,f61])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_xboole_0(X2,X0))
      | ~ sP3(X0,X1,X2) ) ),
    inference(resolution,[],[f69,f79])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ sP3(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f253,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK9(k2_xboole_0(X3,sK8),X4,sK5),sK7)
      | ~ sP2(k2_xboole_0(X3,sK8),X4,sK5)
      | ~ r2_hidden(sK9(k2_xboole_0(X3,sK8),X4,sK5),sK6) ) ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,(
    ! [X4,X3] :
      ( ~ sP2(k2_xboole_0(X3,sK8),X4,sK5)
      | r2_hidden(sK9(k2_xboole_0(X3,sK8),X4,sK5),sK7)
      | ~ r2_hidden(sK9(k2_xboole_0(X3,sK8),X4,sK5),sK6)
      | ~ sP2(k2_xboole_0(X3,sK8),X4,sK5) ) ),
    inference(resolution,[],[f234,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1,sK5),sK8)
      | r2_hidden(sK9(X0,X1,sK5),sK7)
      | ~ r2_hidden(sK9(X0,X1,sK5),sK6)
      | ~ sP2(X0,X1,sK5) ) ),
    inference(resolution,[],[f139,f59])).

fof(f139,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK5)
      | ~ r2_hidden(X0,sK6)
      | r2_hidden(X0,sK7)
      | r2_hidden(X0,sK8) ) ),
    inference(resolution,[],[f138,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f138,plain,(
    ! [X0] :
      ( sP0(sK8,X0,sK7)
      | ~ r2_hidden(X0,sK6)
      | ~ m1_subset_1(X0,sK5) ) ),
    inference(resolution,[],[f48,f56])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ r2_hidden(X1,X3)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f234,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ r2_hidden(sK9(k2_xboole_0(X7,X8),X9,X10),X8)
      | ~ sP2(k2_xboole_0(X7,X8),X9,X10) ) ),
    inference(resolution,[],[f118,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f713,plain,(
    spl11_7 ),
    inference(avatar_contradiction_clause,[],[f712])).

fof(f712,plain,
    ( $false
    | spl11_7 ),
    inference(subsumption_resolution,[],[f711,f54])).

fof(f711,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(sK5))
    | spl11_7 ),
    inference(subsumption_resolution,[],[f708,f55])).

fof(f708,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(sK5))
    | spl11_7 ),
    inference(resolution,[],[f702,f196])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f66,f67])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f702,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK7,sK8),k1_zfmisc_1(sK5))
    | spl11_7 ),
    inference(avatar_component_clause,[],[f700])).

%------------------------------------------------------------------------------

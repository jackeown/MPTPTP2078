%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 184 expanded)
%              Number of leaves         :   31 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  458 ( 675 expanded)
%              Number of equality atoms :  211 ( 274 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f280,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f114,f125,f132,f138,f148,f187,f195,f204,f219,f220,f250,f276,f279])).

fof(f279,plain,(
    ~ spl6_19 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl6_19 ),
    inference(unit_resulting_resolution,[],[f46,f264,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f264,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl6_19
  <=> r2_hidden(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f276,plain,
    ( spl6_19
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f259,f247,f262])).

fof(f247,plain,
    ( spl6_18
  <=> sP0(sK2,sK2,sK2,sK2,sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f259,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl6_18 ),
    inference(resolution,[],[f249,f99])).

fof(f99,plain,(
    ! [X4,X2,X7,X5,X3,X1] :
      ( ~ sP0(X7,X1,X2,X3,X4,X5)
      | r2_hidden(X7,X5) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X0 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ( ( ( sK5(X0,X1,X2,X3,X4,X5) != X0
              & sK5(X0,X1,X2,X3,X4,X5) != X1
              & sK5(X0,X1,X2,X3,X4,X5) != X2
              & sK5(X0,X1,X2,X3,X4,X5) != X3
              & sK5(X0,X1,X2,X3,X4,X5) != X4 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK5(X0,X1,X2,X3,X4,X5) = X0
            | sK5(X0,X1,X2,X3,X4,X5) = X1
            | sK5(X0,X1,X2,X3,X4,X5) = X2
            | sK5(X0,X1,X2,X3,X4,X5) = X3
            | sK5(X0,X1,X2,X3,X4,X5) = X4
            | r2_hidden(sK5(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X0 != X6
              & X1 != X6
              & X2 != X6
              & X3 != X6
              & X4 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X0 = X6
            | X1 = X6
            | X2 = X6
            | X3 = X6
            | X4 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK5(X0,X1,X2,X3,X4,X5) != X0
            & sK5(X0,X1,X2,X3,X4,X5) != X1
            & sK5(X0,X1,X2,X3,X4,X5) != X2
            & sK5(X0,X1,X2,X3,X4,X5) != X3
            & sK5(X0,X1,X2,X3,X4,X5) != X4 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK5(X0,X1,X2,X3,X4,X5) = X0
          | sK5(X0,X1,X2,X3,X4,X5) = X1
          | sK5(X0,X1,X2,X3,X4,X5) = X2
          | sK5(X0,X1,X2,X3,X4,X5) = X3
          | sK5(X0,X1,X2,X3,X4,X5) = X4
          | r2_hidden(sK5(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6
                & X4 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | X4 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( sP0(X4,X3,X2,X1,X0,X5)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

% (2537)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
fof(f249,plain,
    ( sP0(sK2,sK2,sK2,sK2,sK2,k1_xboole_0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f247])).

fof(f250,plain,
    ( spl6_18
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f229,f184,f247])).

fof(f184,plain,
    ( spl6_12
  <=> k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f229,plain,
    ( sP0(sK2,sK2,sK2,sK2,sK2,k1_xboole_0)
    | ~ spl6_12 ),
    inference(superposition,[],[f104,f186])).

fof(f186,plain,
    ( k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f184])).

fof(f104,plain,(
    ! [X4,X2,X0,X3,X1] : sP0(X4,X3,X2,X1,X0,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP0(X4,X3,X2,X1,X0,X5) )
      & ( sP0(X4,X3,X2,X1,X0,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP0(X4,X3,X2,X1,X0,X5) ) ),
    inference(definition_folding,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

fof(f220,plain,
    ( sK1 != k1_relat_1(sK4)
    | r2_hidden(sK3,k1_relat_1(sK4))
    | ~ r2_hidden(sK3,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f219,plain,
    ( ~ spl6_6
    | spl6_15
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f189,f180,f216,f135])).

fof(f135,plain,
    ( spl6_6
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f216,plain,
    ( spl6_15
  <=> sK1 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f180,plain,
    ( spl6_11
  <=> sK1 = k1_relset_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f189,plain,
    ( sK1 = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))))
    | ~ spl6_11 ),
    inference(superposition,[],[f182,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f182,plain,
    ( sK1 = k1_relset_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK4)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f180])).

fof(f204,plain,
    ( ~ spl6_8
    | spl6_4
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f203,f193,f122,f150])).

fof(f150,plain,
    ( spl6_8
  <=> r2_hidden(sK3,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f122,plain,
    ( spl6_4
  <=> sK2 = k1_funct_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f193,plain,
    ( spl6_13
  <=> ! [X0] :
        ( sK2 = k1_funct_1(sK4,X0)
        | ~ r2_hidden(X0,k1_relat_1(sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f203,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK4))
    | spl6_4
    | ~ spl6_13 ),
    inference(trivial_inequality_removal,[],[f198])).

fof(f198,plain,
    ( sK2 != sK2
    | ~ r2_hidden(sK3,k1_relat_1(sK4))
    | spl6_4
    | ~ spl6_13 ),
    inference(superposition,[],[f124,f194])).

fof(f194,plain,
    ( ! [X0] :
        ( sK2 = k1_funct_1(sK4,X0)
        | ~ r2_hidden(X0,k1_relat_1(sK4)) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f193])).

fof(f124,plain,
    ( sK2 != k1_funct_1(sK4,sK3)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f195,plain,
    ( ~ spl6_7
    | ~ spl6_1
    | spl6_13
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f170,f135,f193,f106,f145])).

fof(f145,plain,
    ( spl6_7
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f106,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f170,plain,
    ( ! [X0] :
        ( sK2 = k1_funct_1(sK4,X0)
        | ~ r2_hidden(X0,k1_relat_1(sK4))
        | ~ v1_funct_1(sK4)
        | ~ v1_relat_1(sK4) )
    | ~ spl6_6 ),
    inference(resolution,[],[f160,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f160,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK4)
        | sK2 = X3 )
    | ~ spl6_6 ),
    inference(resolution,[],[f142,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k3_enumset1(X3,X3,X3,X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f66,f84])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f142,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))
        | ~ r2_hidden(X0,sK4) )
    | ~ spl6_6 ),
    inference(resolution,[],[f137,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f137,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f135])).

fof(f187,plain,
    ( spl6_11
    | spl6_12
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f139,f135,f129,f184,f180])).

fof(f129,plain,
    ( spl6_5
  <=> v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f139,plain,
    ( ~ v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | sK1 = k1_relset_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK4)
    | ~ spl6_6 ),
    inference(resolution,[],[f137,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f148,plain,
    ( spl6_7
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f141,f135,f145])).

fof(f141,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_6 ),
    inference(resolution,[],[f137,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f138,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f85,f135])).

fof(f85,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f43,f84])).

fof(f43,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( sK2 != k1_funct_1(sK4,sK3)
    & r2_hidden(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f17,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK2 != k1_funct_1(sK4,sK3)
      & r2_hidden(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
      & v1_funct_2(sK4,sK1,k1_tarski(sK2))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f132,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f86,f129])).

fof(f86,plain,(
    v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f42,f84])).

fof(f42,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f125,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f45,f122])).

fof(f45,plain,(
    sK2 != k1_funct_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f114,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f44,f111])).

fof(f111,plain,
    ( spl6_2
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f44,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f109,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f41,f106])).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:07:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (2472)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.50  % (2472)Refutation not found, incomplete strategy% (2472)------------------------------
% 0.22/0.50  % (2472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (2472)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (2472)Memory used [KB]: 1791
% 0.22/0.50  % (2472)Time elapsed: 0.056 s
% 0.22/0.50  % (2472)------------------------------
% 0.22/0.50  % (2472)------------------------------
% 0.22/0.54  % (2482)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (2481)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (2474)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (2473)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.56  % (2481)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (2489)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (2493)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.52/0.57  % SZS output start Proof for theBenchmark
% 1.52/0.57  fof(f280,plain,(
% 1.52/0.57    $false),
% 1.52/0.57    inference(avatar_sat_refutation,[],[f109,f114,f125,f132,f138,f148,f187,f195,f204,f219,f220,f250,f276,f279])).
% 1.52/0.57  fof(f279,plain,(
% 1.52/0.57    ~spl6_19),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f277])).
% 1.52/0.57  fof(f277,plain,(
% 1.52/0.57    $false | ~spl6_19),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f46,f264,f54])).
% 1.52/0.57  fof(f54,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f21])).
% 1.52/0.57  fof(f21,plain,(
% 1.52/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f10])).
% 1.52/0.57  fof(f10,axiom,(
% 1.52/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.52/0.57  fof(f264,plain,(
% 1.52/0.57    r2_hidden(sK2,k1_xboole_0) | ~spl6_19),
% 1.52/0.57    inference(avatar_component_clause,[],[f262])).
% 1.52/0.57  fof(f262,plain,(
% 1.52/0.57    spl6_19 <=> r2_hidden(sK2,k1_xboole_0)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.52/0.57  fof(f46,plain,(
% 1.52/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f1])).
% 1.52/0.57  fof(f1,axiom,(
% 1.52/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.52/0.57  fof(f276,plain,(
% 1.52/0.57    spl6_19 | ~spl6_18),
% 1.52/0.57    inference(avatar_split_clause,[],[f259,f247,f262])).
% 1.52/0.57  fof(f247,plain,(
% 1.52/0.57    spl6_18 <=> sP0(sK2,sK2,sK2,sK2,sK2,k1_xboole_0)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.52/0.57  fof(f259,plain,(
% 1.52/0.57    r2_hidden(sK2,k1_xboole_0) | ~spl6_18),
% 1.52/0.57    inference(resolution,[],[f249,f99])).
% 1.52/0.57  fof(f99,plain,(
% 1.52/0.57    ( ! [X4,X2,X7,X5,X3,X1] : (~sP0(X7,X1,X2,X3,X4,X5) | r2_hidden(X7,X5)) )),
% 1.52/0.57    inference(equality_resolution,[],[f73])).
% 1.52/0.57  fof(f73,plain,(
% 1.52/0.57    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X0 != X7 | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f39])).
% 1.52/0.57  fof(f39,plain,(
% 1.52/0.57    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | (((sK5(X0,X1,X2,X3,X4,X5) != X0 & sK5(X0,X1,X2,X3,X4,X5) != X1 & sK5(X0,X1,X2,X3,X4,X5) != X2 & sK5(X0,X1,X2,X3,X4,X5) != X3 & sK5(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5),X5)) & (sK5(X0,X1,X2,X3,X4,X5) = X0 | sK5(X0,X1,X2,X3,X4,X5) = X1 | sK5(X0,X1,X2,X3,X4,X5) = X2 | sK5(X0,X1,X2,X3,X4,X5) = X3 | sK5(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK5(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 1.52/0.57  fof(f38,plain,(
% 1.52/0.57    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5))) => (((sK5(X0,X1,X2,X3,X4,X5) != X0 & sK5(X0,X1,X2,X3,X4,X5) != X1 & sK5(X0,X1,X2,X3,X4,X5) != X2 & sK5(X0,X1,X2,X3,X4,X5) != X3 & sK5(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5),X5)) & (sK5(X0,X1,X2,X3,X4,X5) = X0 | sK5(X0,X1,X2,X3,X4,X5) = X1 | sK5(X0,X1,X2,X3,X4,X5) = X2 | sK5(X0,X1,X2,X3,X4,X5) = X3 | sK5(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK5(X0,X1,X2,X3,X4,X5),X5))))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f37,plain,(
% 1.52/0.57    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | ? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 1.52/0.57    inference(rectify,[],[f36])).
% 1.52/0.57  fof(f36,plain,(
% 1.52/0.57    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 1.52/0.57    inference(flattening,[],[f35])).
% 1.52/0.57  fof(f35,plain,(
% 1.52/0.57    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 1.52/0.57    inference(nnf_transformation,[],[f27])).
% 1.52/0.57  fof(f27,plain,(
% 1.52/0.57    ! [X4,X3,X2,X1,X0,X5] : (sP0(X4,X3,X2,X1,X0,X5) <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 1.52/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.52/0.58  % (2537)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.52/0.58  fof(f249,plain,(
% 1.52/0.58    sP0(sK2,sK2,sK2,sK2,sK2,k1_xboole_0) | ~spl6_18),
% 1.52/0.58    inference(avatar_component_clause,[],[f247])).
% 1.52/0.58  fof(f250,plain,(
% 1.52/0.58    spl6_18 | ~spl6_12),
% 1.52/0.58    inference(avatar_split_clause,[],[f229,f184,f247])).
% 1.52/0.58  fof(f184,plain,(
% 1.52/0.58    spl6_12 <=> k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.52/0.58  fof(f229,plain,(
% 1.52/0.58    sP0(sK2,sK2,sK2,sK2,sK2,k1_xboole_0) | ~spl6_12),
% 1.52/0.58    inference(superposition,[],[f104,f186])).
% 1.52/0.58  fof(f186,plain,(
% 1.52/0.58    k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | ~spl6_12),
% 1.52/0.58    inference(avatar_component_clause,[],[f184])).
% 1.52/0.58  fof(f104,plain,(
% 1.52/0.58    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0,k3_enumset1(X0,X1,X2,X3,X4))) )),
% 1.52/0.58    inference(equality_resolution,[],[f80])).
% 1.52/0.58  fof(f80,plain,(
% 1.52/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 1.52/0.58    inference(cnf_transformation,[],[f40])).
% 1.52/0.58  fof(f40,plain,(
% 1.52/0.58    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ~sP0(X4,X3,X2,X1,X0,X5)) & (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 1.52/0.58    inference(nnf_transformation,[],[f28])).
% 1.52/0.58  fof(f28,plain,(
% 1.52/0.58    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> sP0(X4,X3,X2,X1,X0,X5))),
% 1.52/0.58    inference(definition_folding,[],[f26,f27])).
% 1.52/0.58  fof(f26,plain,(
% 1.52/0.58    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 1.52/0.58    inference(ennf_transformation,[],[f7])).
% 1.52/0.58  fof(f7,axiom,(
% 1.52/0.58    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 1.52/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).
% 1.52/0.58  fof(f220,plain,(
% 1.52/0.58    sK1 != k1_relat_1(sK4) | r2_hidden(sK3,k1_relat_1(sK4)) | ~r2_hidden(sK3,sK1)),
% 1.52/0.58    introduced(theory_tautology_sat_conflict,[])).
% 1.52/0.58  fof(f219,plain,(
% 1.52/0.58    ~spl6_6 | spl6_15 | ~spl6_11),
% 1.52/0.58    inference(avatar_split_clause,[],[f189,f180,f216,f135])).
% 1.52/0.58  fof(f135,plain,(
% 1.52/0.58    spl6_6 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.52/0.58  fof(f216,plain,(
% 1.52/0.58    spl6_15 <=> sK1 = k1_relat_1(sK4)),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.52/0.58  fof(f180,plain,(
% 1.52/0.58    spl6_11 <=> sK1 = k1_relset_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK4)),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.52/0.58  fof(f189,plain,(
% 1.52/0.58    sK1 = k1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) | ~spl6_11),
% 1.52/0.58    inference(superposition,[],[f182,f57])).
% 1.52/0.58  fof(f57,plain,(
% 1.52/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.52/0.58    inference(cnf_transformation,[],[f23])).
% 1.52/0.58  fof(f23,plain,(
% 1.52/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.58    inference(ennf_transformation,[],[f12])).
% 1.52/0.58  fof(f12,axiom,(
% 1.52/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.52/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.52/0.58  fof(f182,plain,(
% 1.52/0.58    sK1 = k1_relset_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK4) | ~spl6_11),
% 1.52/0.58    inference(avatar_component_clause,[],[f180])).
% 1.52/0.58  fof(f204,plain,(
% 1.52/0.58    ~spl6_8 | spl6_4 | ~spl6_13),
% 1.52/0.58    inference(avatar_split_clause,[],[f203,f193,f122,f150])).
% 1.52/0.58  fof(f150,plain,(
% 1.52/0.58    spl6_8 <=> r2_hidden(sK3,k1_relat_1(sK4))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.52/0.58  fof(f122,plain,(
% 1.52/0.58    spl6_4 <=> sK2 = k1_funct_1(sK4,sK3)),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.52/0.58  fof(f193,plain,(
% 1.52/0.58    spl6_13 <=> ! [X0] : (sK2 = k1_funct_1(sK4,X0) | ~r2_hidden(X0,k1_relat_1(sK4)))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.52/0.58  fof(f203,plain,(
% 1.52/0.58    ~r2_hidden(sK3,k1_relat_1(sK4)) | (spl6_4 | ~spl6_13)),
% 1.52/0.58    inference(trivial_inequality_removal,[],[f198])).
% 1.52/0.58  fof(f198,plain,(
% 1.52/0.58    sK2 != sK2 | ~r2_hidden(sK3,k1_relat_1(sK4)) | (spl6_4 | ~spl6_13)),
% 1.52/0.58    inference(superposition,[],[f124,f194])).
% 1.52/0.58  fof(f194,plain,(
% 1.52/0.58    ( ! [X0] : (sK2 = k1_funct_1(sK4,X0) | ~r2_hidden(X0,k1_relat_1(sK4))) ) | ~spl6_13),
% 1.52/0.58    inference(avatar_component_clause,[],[f193])).
% 1.52/0.58  fof(f124,plain,(
% 1.52/0.58    sK2 != k1_funct_1(sK4,sK3) | spl6_4),
% 1.52/0.58    inference(avatar_component_clause,[],[f122])).
% 1.52/0.58  fof(f195,plain,(
% 1.52/0.58    ~spl6_7 | ~spl6_1 | spl6_13 | ~spl6_6),
% 1.52/0.58    inference(avatar_split_clause,[],[f170,f135,f193,f106,f145])).
% 1.52/0.58  fof(f145,plain,(
% 1.52/0.58    spl6_7 <=> v1_relat_1(sK4)),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.52/0.58  fof(f106,plain,(
% 1.52/0.58    spl6_1 <=> v1_funct_1(sK4)),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.52/0.58  fof(f170,plain,(
% 1.52/0.58    ( ! [X0] : (sK2 = k1_funct_1(sK4,X0) | ~r2_hidden(X0,k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) ) | ~spl6_6),
% 1.52/0.58    inference(resolution,[],[f160,f92])).
% 1.52/0.58  fof(f92,plain,(
% 1.52/0.58    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.58    inference(equality_resolution,[],[f48])).
% 1.52/0.58  fof(f48,plain,(
% 1.52/0.58    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.58    inference(cnf_transformation,[],[f31])).
% 1.52/0.58  fof(f31,plain,(
% 1.52/0.58    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.58    inference(nnf_transformation,[],[f19])).
% 1.52/0.58  fof(f19,plain,(
% 1.52/0.58    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.58    inference(flattening,[],[f18])).
% 1.52/0.58  fof(f18,plain,(
% 1.52/0.58    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.52/0.58    inference(ennf_transformation,[],[f9])).
% 1.52/0.58  fof(f9,axiom,(
% 1.52/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 1.52/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 1.52/0.58  fof(f160,plain,(
% 1.52/0.58    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK4) | sK2 = X3) ) | ~spl6_6),
% 1.52/0.58    inference(resolution,[],[f142,f88])).
% 1.52/0.58  fof(f88,plain,(
% 1.52/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k3_enumset1(X3,X3,X3,X3,X3))) | X1 = X3) )),
% 1.52/0.58    inference(definition_unfolding,[],[f66,f84])).
% 1.52/0.58  fof(f84,plain,(
% 1.52/0.58    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.52/0.58    inference(definition_unfolding,[],[f47,f83])).
% 1.52/0.58  fof(f83,plain,(
% 1.52/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.52/0.58    inference(definition_unfolding,[],[f52,f82])).
% 1.52/0.58  fof(f82,plain,(
% 1.52/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.52/0.58    inference(definition_unfolding,[],[f55,f64])).
% 1.52/0.58  fof(f64,plain,(
% 1.52/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.52/0.58    inference(cnf_transformation,[],[f5])).
% 1.52/0.58  fof(f5,axiom,(
% 1.52/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.52/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.52/0.58  fof(f55,plain,(
% 1.52/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.52/0.58    inference(cnf_transformation,[],[f4])).
% 1.52/0.58  fof(f4,axiom,(
% 1.52/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.52/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.52/0.58  fof(f52,plain,(
% 1.52/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.52/0.58    inference(cnf_transformation,[],[f3])).
% 1.52/0.58  fof(f3,axiom,(
% 1.52/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.52/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.52/0.58  fof(f47,plain,(
% 1.52/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.52/0.58    inference(cnf_transformation,[],[f2])).
% 1.52/0.58  fof(f2,axiom,(
% 1.52/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.52/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.52/0.58  fof(f66,plain,(
% 1.52/0.58    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 1.52/0.58    inference(cnf_transformation,[],[f34])).
% 1.52/0.58  fof(f34,plain,(
% 1.52/0.58    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 1.52/0.58    inference(flattening,[],[f33])).
% 1.52/0.58  fof(f33,plain,(
% 1.52/0.58    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 1.52/0.58    inference(nnf_transformation,[],[f6])).
% 1.52/0.58  fof(f6,axiom,(
% 1.52/0.58    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 1.52/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 1.52/0.58  fof(f142,plain,(
% 1.52/0.58    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) | ~r2_hidden(X0,sK4)) ) | ~spl6_6),
% 1.52/0.58    inference(resolution,[],[f137,f53])).
% 1.52/0.58  fof(f53,plain,(
% 1.52/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.52/0.58    inference(cnf_transformation,[],[f20])).
% 1.52/0.58  fof(f20,plain,(
% 1.52/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.52/0.58    inference(ennf_transformation,[],[f8])).
% 1.52/0.58  fof(f8,axiom,(
% 1.52/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.52/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.52/0.58  fof(f137,plain,(
% 1.52/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) | ~spl6_6),
% 1.52/0.58    inference(avatar_component_clause,[],[f135])).
% 1.52/0.58  fof(f187,plain,(
% 1.52/0.58    spl6_11 | spl6_12 | ~spl6_5 | ~spl6_6),
% 1.52/0.58    inference(avatar_split_clause,[],[f139,f135,f129,f184,f180])).
% 1.52/0.58  fof(f129,plain,(
% 1.52/0.58    spl6_5 <=> v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.52/0.58  fof(f139,plain,(
% 1.52/0.58    ~v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | sK1 = k1_relset_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK4) | ~spl6_6),
% 1.52/0.58    inference(resolution,[],[f137,f58])).
% 1.52/0.58  fof(f58,plain,(
% 1.52/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.52/0.58    inference(cnf_transformation,[],[f32])).
% 1.74/0.58  fof(f32,plain,(
% 1.74/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.58    inference(nnf_transformation,[],[f25])).
% 1.74/0.58  fof(f25,plain,(
% 1.74/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.58    inference(flattening,[],[f24])).
% 1.74/0.58  fof(f24,plain,(
% 1.74/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.58    inference(ennf_transformation,[],[f13])).
% 1.74/0.58  fof(f13,axiom,(
% 1.74/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.74/0.58  fof(f148,plain,(
% 1.74/0.58    spl6_7 | ~spl6_6),
% 1.74/0.58    inference(avatar_split_clause,[],[f141,f135,f145])).
% 1.74/0.58  fof(f141,plain,(
% 1.74/0.58    v1_relat_1(sK4) | ~spl6_6),
% 1.74/0.58    inference(resolution,[],[f137,f56])).
% 1.74/0.58  fof(f56,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f22])).
% 1.74/0.58  fof(f22,plain,(
% 1.74/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.58    inference(ennf_transformation,[],[f11])).
% 1.74/0.58  fof(f11,axiom,(
% 1.74/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.74/0.58  fof(f138,plain,(
% 1.74/0.58    spl6_6),
% 1.74/0.58    inference(avatar_split_clause,[],[f85,f135])).
% 1.74/0.58  fof(f85,plain,(
% 1.74/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))))),
% 1.74/0.58    inference(definition_unfolding,[],[f43,f84])).
% 1.74/0.58  fof(f43,plain,(
% 1.74/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 1.74/0.58    inference(cnf_transformation,[],[f30])).
% 1.74/0.58  fof(f30,plain,(
% 1.74/0.58    sK2 != k1_funct_1(sK4,sK3) & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4)),
% 1.74/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f17,f29])).
% 1.74/0.58  fof(f29,plain,(
% 1.74/0.58    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK2 != k1_funct_1(sK4,sK3) & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4))),
% 1.74/0.58    introduced(choice_axiom,[])).
% 1.74/0.58  fof(f17,plain,(
% 1.74/0.58    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.74/0.58    inference(flattening,[],[f16])).
% 1.74/0.58  fof(f16,plain,(
% 1.74/0.58    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.74/0.58    inference(ennf_transformation,[],[f15])).
% 1.74/0.58  fof(f15,negated_conjecture,(
% 1.74/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.74/0.58    inference(negated_conjecture,[],[f14])).
% 1.74/0.58  fof(f14,conjecture,(
% 1.74/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 1.74/0.58  fof(f132,plain,(
% 1.74/0.58    spl6_5),
% 1.74/0.58    inference(avatar_split_clause,[],[f86,f129])).
% 1.74/0.58  fof(f86,plain,(
% 1.74/0.58    v1_funct_2(sK4,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 1.74/0.58    inference(definition_unfolding,[],[f42,f84])).
% 1.74/0.58  fof(f42,plain,(
% 1.74/0.58    v1_funct_2(sK4,sK1,k1_tarski(sK2))),
% 1.74/0.58    inference(cnf_transformation,[],[f30])).
% 1.74/0.58  fof(f125,plain,(
% 1.74/0.58    ~spl6_4),
% 1.74/0.58    inference(avatar_split_clause,[],[f45,f122])).
% 1.74/0.58  fof(f45,plain,(
% 1.74/0.58    sK2 != k1_funct_1(sK4,sK3)),
% 1.74/0.58    inference(cnf_transformation,[],[f30])).
% 1.74/0.58  fof(f114,plain,(
% 1.74/0.58    spl6_2),
% 1.74/0.58    inference(avatar_split_clause,[],[f44,f111])).
% 1.74/0.58  fof(f111,plain,(
% 1.74/0.58    spl6_2 <=> r2_hidden(sK3,sK1)),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.74/0.58  fof(f44,plain,(
% 1.74/0.58    r2_hidden(sK3,sK1)),
% 1.74/0.58    inference(cnf_transformation,[],[f30])).
% 1.74/0.58  fof(f109,plain,(
% 1.74/0.58    spl6_1),
% 1.74/0.58    inference(avatar_split_clause,[],[f41,f106])).
% 1.74/0.58  fof(f41,plain,(
% 1.74/0.58    v1_funct_1(sK4)),
% 1.74/0.58    inference(cnf_transformation,[],[f30])).
% 1.74/0.58  % SZS output end Proof for theBenchmark
% 1.74/0.58  % (2481)------------------------------
% 1.74/0.58  % (2481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.59  % (2481)Termination reason: Refutation
% 1.74/0.59  
% 1.74/0.59  % (2481)Memory used [KB]: 10874
% 1.74/0.59  % (2481)Time elapsed: 0.126 s
% 1.74/0.59  % (2481)------------------------------
% 1.74/0.59  % (2481)------------------------------
% 1.74/0.59  % (2470)Success in time 0.213 s
%------------------------------------------------------------------------------

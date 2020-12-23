%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 284 expanded)
%              Number of leaves         :   32 ( 114 expanded)
%              Depth                    :   11
%              Number of atoms          :  496 (1081 expanded)
%              Number of equality atoms :  176 ( 437 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f555,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f106,f116,f121,f126,f132,f238,f250,f264,f270,f302,f327,f354,f385,f417,f425,f438,f550,f554])).

fof(f554,plain,
    ( ~ spl8_28
    | spl8_38 ),
    inference(avatar_contradiction_clause,[],[f551])).

fof(f551,plain,
    ( $false
    | ~ spl8_28
    | spl8_38 ),
    inference(unit_resulting_resolution,[],[f384,f549,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f549,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | spl8_38 ),
    inference(avatar_component_clause,[],[f547])).

fof(f547,plain,
    ( spl8_38
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f384,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f382])).

fof(f382,plain,
    ( spl8_28
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f550,plain,
    ( ~ spl8_38
    | spl8_6
    | ~ spl8_17
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f545,f324,f261,f123,f547])).

fof(f123,plain,
    ( spl8_6
  <=> k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) = k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f261,plain,
    ( spl8_17
  <=> k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f324,plain,
    ( spl8_25
  <=> k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f545,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | spl8_6
    | ~ spl8_17
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f536,f326])).

fof(f326,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f324])).

fof(f536,plain,
    ( k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2)
    | spl8_6
    | ~ spl8_17 ),
    inference(superposition,[],[f125,f263])).

fof(f263,plain,
    ( k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f261])).

fof(f125,plain,
    ( k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) != k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f438,plain,
    ( spl8_14
    | ~ spl8_15
    | ~ spl8_33 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | spl8_14
    | ~ spl8_15
    | ~ spl8_33 ),
    inference(unit_resulting_resolution,[],[f249,f244,f424])).

fof(f424,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK0) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl8_33
  <=> ! [X0] :
        ( k1_funct_1(sK2,sK0) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f244,plain,
    ( k1_funct_1(sK2,sK0) != sK7(k1_funct_1(sK2,sK0),k2_relat_1(sK2))
    | spl8_14 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl8_14
  <=> k1_funct_1(sK2,sK0) = sK7(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f249,plain,
    ( r2_hidden(sK7(k1_funct_1(sK2,sK0),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl8_15
  <=> r2_hidden(sK7(k1_funct_1(sK2,sK0),k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f425,plain,
    ( ~ spl8_7
    | ~ spl8_1
    | spl8_33
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f421,f415,f423,f98,f129])).

fof(f129,plain,
    ( spl8_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f98,plain,
    ( spl8_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f415,plain,
    ( spl8_32
  <=> ! [X1] :
        ( sK0 = sK5(sK2,X1)
        | ~ r2_hidden(X1,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f421,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK0) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_32 ),
    inference(duplicate_literal_removal,[],[f418])).

fof(f418,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK0) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl8_32 ),
    inference(superposition,[],[f87,f416])).

fof(f416,plain,
    ( ! [X1] :
        ( sK0 = sK5(sK2,X1)
        | ~ r2_hidden(X1,k2_relat_1(sK2)) )
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f415])).

fof(f87,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
                  & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                    & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).

fof(f30,plain,(
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
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK3(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

% (23151)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f417,plain,
    ( ~ spl8_7
    | ~ spl8_1
    | spl8_32
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f369,f324,f415,f98,f129])).

fof(f369,plain,
    ( ! [X1] :
        ( sK0 = sK5(sK2,X1)
        | ~ r2_hidden(X1,k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_25 ),
    inference(resolution,[],[f343,f88])).

fof(f88,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f343,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK2))
        | sK0 = X4 )
    | ~ spl8_25 ),
    inference(superposition,[],[f96,f326])).

fof(f96,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f67,f74])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f71,f73])).

fof(f73,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f385,plain,
    ( spl8_28
    | ~ spl8_5
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f334,f324,f118,f382])).

fof(f118,plain,
    ( spl8_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f334,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl8_5
    | ~ spl8_25 ),
    inference(superposition,[],[f120,f326])).

fof(f120,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f354,plain,
    ( spl8_18
    | ~ spl8_25 ),
    inference(avatar_contradiction_clause,[],[f352])).

fof(f352,plain,
    ( $false
    | spl8_18
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f269,f342])).

fof(f342,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl8_25 ),
    inference(superposition,[],[f95,f326])).

fof(f95,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f68,f74])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f269,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl8_18 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl8_18
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f327,plain,
    ( ~ spl8_5
    | spl8_25
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f308,f299,f324,f118])).

fof(f299,plain,
    ( spl8_24
  <=> k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f308,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | ~ spl8_24 ),
    inference(superposition,[],[f301,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f301,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f299])).

fof(f302,plain,
    ( spl8_24
    | spl8_2
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f288,f118,f113,f103,f299])).

fof(f103,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f113,plain,
    ( spl8_4
  <=> v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f288,plain,
    ( ~ v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1)
    | k1_xboole_0 = sK1
    | k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2)
    | ~ spl8_5 ),
    inference(resolution,[],[f54,f120])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f270,plain,
    ( ~ spl8_7
    | ~ spl8_1
    | ~ spl8_18
    | spl8_16 ),
    inference(avatar_split_clause,[],[f265,f257,f267,f98,f129])).

fof(f257,plain,
    ( spl8_16
  <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f265,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl8_16 ),
    inference(resolution,[],[f259,f86])).

fof(f86,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f259,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))
    | spl8_16 ),
    inference(avatar_component_clause,[],[f257])).

fof(f264,plain,
    ( ~ spl8_16
    | spl8_17
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f255,f243,f261,f257])).

fof(f255,plain,
    ( k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))
    | ~ spl8_14 ),
    inference(trivial_inequality_removal,[],[f254])).

fof(f254,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0)
    | k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))
    | ~ spl8_14 ),
    inference(superposition,[],[f80,f245])).

fof(f245,plain,
    ( k1_funct_1(sK2,sK0) = sK7(k1_funct_1(sK2,sK0),k2_relat_1(sK2))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f243])).

fof(f80,plain,(
    ! [X0,X1] :
      ( sK7(X0,X1) != X0
      | k1_enumset1(X0,X0,X0) = X1
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f70,f74])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK7(X0,X1) != X0
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f250,plain,
    ( spl8_14
    | spl8_15
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f241,f236,f247,f243])).

fof(f236,plain,
    ( spl8_13
  <=> ! [X0] :
        ( k2_relat_1(sK2) != X0
        | r2_hidden(sK7(k1_funct_1(sK2,sK0),X0),X0)
        | k1_funct_1(sK2,sK0) = sK7(k1_funct_1(sK2,sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f241,plain,
    ( r2_hidden(sK7(k1_funct_1(sK2,sK0),k2_relat_1(sK2)),k2_relat_1(sK2))
    | k1_funct_1(sK2,sK0) = sK7(k1_funct_1(sK2,sK0),k2_relat_1(sK2))
    | ~ spl8_13 ),
    inference(equality_resolution,[],[f237])).

fof(f237,plain,
    ( ! [X0] :
        ( k2_relat_1(sK2) != X0
        | r2_hidden(sK7(k1_funct_1(sK2,sK0),X0),X0)
        | k1_funct_1(sK2,sK0) = sK7(k1_funct_1(sK2,sK0),X0) )
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f236])).

fof(f238,plain,
    ( ~ spl8_5
    | spl8_13
    | spl8_6 ),
    inference(avatar_split_clause,[],[f229,f123,f236,f118])).

fof(f229,plain,
    ( ! [X0] :
        ( k2_relat_1(sK2) != X0
        | k1_funct_1(sK2,sK0) = sK7(k1_funct_1(sK2,sK0),X0)
        | r2_hidden(sK7(k1_funct_1(sK2,sK0),X0),X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) )
    | spl8_6 ),
    inference(superposition,[],[f205,f53])).

fof(f205,plain,
    ( ! [X17] :
        ( k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) != X17
        | k1_funct_1(sK2,sK0) = sK7(k1_funct_1(sK2,sK0),X17)
        | r2_hidden(sK7(k1_funct_1(sK2,sK0),X17),X17) )
    | spl8_6 ),
    inference(superposition,[],[f125,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = X1
      | sK7(X0,X1) = X0
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK7(X0,X1) = X0
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f132,plain,
    ( spl8_7
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f127,f118,f129])).

fof(f127,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_5 ),
    inference(resolution,[],[f66,f120])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f126,plain,(
    ~ spl8_6 ),
    inference(avatar_split_clause,[],[f75,f123])).

fof(f75,plain,(
    k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) != k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f46,f74,f74])).

fof(f46,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(f121,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f76,f118])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f44,f74])).

% (23140)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f116,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f77,f113])).

fof(f77,plain,(
    v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f43,f74])).

fof(f43,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f106,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f45,f103])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f101,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f42,f98])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:31:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (23129)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (23147)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.50  % (23125)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.50  % (23139)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.50  % (23153)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (23153)Refutation not found, incomplete strategy% (23153)------------------------------
% 0.21/0.50  % (23153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23153)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (23153)Memory used [KB]: 1663
% 0.21/0.50  % (23153)Time elapsed: 0.110 s
% 0.21/0.50  % (23153)------------------------------
% 0.21/0.50  % (23153)------------------------------
% 0.21/0.51  % (23145)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (23152)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.51  % (23130)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (23135)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (23137)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (23134)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (23136)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (23132)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (23123)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (23148)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (23146)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (23122)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (23126)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (23127)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (23128)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (23147)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (23144)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f555,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f101,f106,f116,f121,f126,f132,f238,f250,f264,f270,f302,f327,f354,f385,f417,f425,f438,f550,f554])).
% 0.21/0.54  fof(f554,plain,(
% 0.21/0.54    ~spl8_28 | spl8_38),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f551])).
% 0.21/0.54  fof(f551,plain,(
% 0.21/0.54    $false | (~spl8_28 | spl8_38)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f384,f549,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.54  fof(f549,plain,(
% 0.21/0.54    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | spl8_38),
% 0.21/0.54    inference(avatar_component_clause,[],[f547])).
% 0.21/0.54  fof(f547,plain,(
% 0.21/0.54    spl8_38 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 0.21/0.54  fof(f384,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~spl8_28),
% 0.21/0.54    inference(avatar_component_clause,[],[f382])).
% 0.21/0.54  fof(f382,plain,(
% 0.21/0.54    spl8_28 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.21/0.54  fof(f550,plain,(
% 0.21/0.54    ~spl8_38 | spl8_6 | ~spl8_17 | ~spl8_25),
% 0.21/0.54    inference(avatar_split_clause,[],[f545,f324,f261,f123,f547])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    spl8_6 <=> k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) = k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.54  fof(f261,plain,(
% 0.21/0.54    spl8_17 <=> k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.54  fof(f324,plain,(
% 0.21/0.54    spl8_25 <=> k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.54  fof(f545,plain,(
% 0.21/0.54    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | (spl8_6 | ~spl8_17 | ~spl8_25)),
% 0.21/0.54    inference(forward_demodulation,[],[f536,f326])).
% 0.21/0.54  fof(f326,plain,(
% 0.21/0.54    k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2) | ~spl8_25),
% 0.21/0.54    inference(avatar_component_clause,[],[f324])).
% 0.21/0.54  fof(f536,plain,(
% 0.21/0.54    k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2) | (spl8_6 | ~spl8_17)),
% 0.21/0.54    inference(superposition,[],[f125,f263])).
% 0.21/0.54  fof(f263,plain,(
% 0.21/0.54    k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | ~spl8_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f261])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) != k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) | spl8_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f123])).
% 0.21/0.54  fof(f438,plain,(
% 0.21/0.54    spl8_14 | ~spl8_15 | ~spl8_33),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f426])).
% 0.21/0.54  fof(f426,plain,(
% 0.21/0.54    $false | (spl8_14 | ~spl8_15 | ~spl8_33)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f249,f244,f424])).
% 0.21/0.54  fof(f424,plain,(
% 0.21/0.54    ( ! [X0] : (k1_funct_1(sK2,sK0) = X0 | ~r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl8_33),
% 0.21/0.54    inference(avatar_component_clause,[],[f423])).
% 0.21/0.54  fof(f423,plain,(
% 0.21/0.54    spl8_33 <=> ! [X0] : (k1_funct_1(sK2,sK0) = X0 | ~r2_hidden(X0,k2_relat_1(sK2)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.21/0.54  fof(f244,plain,(
% 0.21/0.54    k1_funct_1(sK2,sK0) != sK7(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) | spl8_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f243])).
% 0.21/0.54  fof(f243,plain,(
% 0.21/0.54    spl8_14 <=> k1_funct_1(sK2,sK0) = sK7(k1_funct_1(sK2,sK0),k2_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.54  fof(f249,plain,(
% 0.21/0.54    r2_hidden(sK7(k1_funct_1(sK2,sK0),k2_relat_1(sK2)),k2_relat_1(sK2)) | ~spl8_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f247])).
% 0.21/0.54  fof(f247,plain,(
% 0.21/0.54    spl8_15 <=> r2_hidden(sK7(k1_funct_1(sK2,sK0),k2_relat_1(sK2)),k2_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.54  fof(f425,plain,(
% 0.21/0.54    ~spl8_7 | ~spl8_1 | spl8_33 | ~spl8_32),
% 0.21/0.54    inference(avatar_split_clause,[],[f421,f415,f423,f98,f129])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    spl8_7 <=> v1_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    spl8_1 <=> v1_funct_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.54  fof(f415,plain,(
% 0.21/0.54    spl8_32 <=> ! [X1] : (sK0 = sK5(sK2,X1) | ~r2_hidden(X1,k2_relat_1(sK2)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.21/0.54  fof(f421,plain,(
% 0.21/0.54    ( ! [X0] : (k1_funct_1(sK2,sK0) = X0 | ~r2_hidden(X0,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl8_32),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f418])).
% 0.21/0.54  fof(f418,plain,(
% 0.21/0.54    ( ! [X0] : (k1_funct_1(sK2,sK0) = X0 | ~r2_hidden(X0,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl8_32),
% 0.21/0.54    inference(superposition,[],[f87,f416])).
% 0.21/0.54  fof(f416,plain,(
% 0.21/0.54    ( ! [X1] : (sK0 = sK5(sK2,X1) | ~r2_hidden(X1,k2_relat_1(sK2))) ) | ~spl8_32),
% 0.21/0.54    inference(avatar_component_clause,[],[f415])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X0,X5] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(rectify,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.54  % (23151)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  fof(f417,plain,(
% 0.21/0.54    ~spl8_7 | ~spl8_1 | spl8_32 | ~spl8_25),
% 0.21/0.54    inference(avatar_split_clause,[],[f369,f324,f415,f98,f129])).
% 0.21/0.54  fof(f369,plain,(
% 0.21/0.54    ( ! [X1] : (sK0 = sK5(sK2,X1) | ~r2_hidden(X1,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl8_25),
% 0.21/0.54    inference(resolution,[],[f343,f88])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X0,X5] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f343,plain,(
% 0.21/0.54    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK2)) | sK0 = X4) ) | ~spl8_25),
% 0.21/0.54    inference(superposition,[],[f96,f326])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_enumset1(X0,X0,X0)) | X0 = X3) )),
% 0.21/0.54    inference(equality_resolution,[],[f83])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.21/0.54    inference(definition_unfolding,[],[f67,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f71,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.54    inference(rectify,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.54  fof(f385,plain,(
% 0.21/0.54    spl8_28 | ~spl8_5 | ~spl8_25),
% 0.21/0.54    inference(avatar_split_clause,[],[f334,f324,f118,f382])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    spl8_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.54  fof(f334,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | (~spl8_5 | ~spl8_25)),
% 0.21/0.54    inference(superposition,[],[f120,f326])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) | ~spl8_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f118])).
% 0.21/0.54  fof(f354,plain,(
% 0.21/0.54    spl8_18 | ~spl8_25),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f352])).
% 0.21/0.54  fof(f352,plain,(
% 0.21/0.54    $false | (spl8_18 | ~spl8_25)),
% 0.21/0.54    inference(subsumption_resolution,[],[f269,f342])).
% 0.21/0.54  fof(f342,plain,(
% 0.21/0.54    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl8_25),
% 0.21/0.54    inference(superposition,[],[f95,f326])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 0.21/0.54    inference(equality_resolution,[],[f94])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 0.21/0.54    inference(equality_resolution,[],[f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 0.21/0.54    inference(definition_unfolding,[],[f68,f74])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f269,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl8_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f267])).
% 0.21/0.54  fof(f267,plain,(
% 0.21/0.54    spl8_18 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.54  fof(f327,plain,(
% 0.21/0.54    ~spl8_5 | spl8_25 | ~spl8_24),
% 0.21/0.54    inference(avatar_split_clause,[],[f308,f299,f324,f118])).
% 0.21/0.54  fof(f299,plain,(
% 0.21/0.54    spl8_24 <=> k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.21/0.54  fof(f308,plain,(
% 0.21/0.54    k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) | ~spl8_24),
% 0.21/0.54    inference(superposition,[],[f301,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f301,plain,(
% 0.21/0.54    k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) | ~spl8_24),
% 0.21/0.54    inference(avatar_component_clause,[],[f299])).
% 0.21/0.54  fof(f302,plain,(
% 0.21/0.54    spl8_24 | spl8_2 | ~spl8_4 | ~spl8_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f288,f118,f113,f103,f299])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    spl8_2 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    spl8_4 <=> v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.54  fof(f288,plain,(
% 0.21/0.54    ~v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1) | k1_xboole_0 = sK1 | k1_enumset1(sK0,sK0,sK0) = k1_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) | ~spl8_5),
% 0.21/0.54    inference(resolution,[],[f54,f120])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.54  fof(f270,plain,(
% 0.21/0.54    ~spl8_7 | ~spl8_1 | ~spl8_18 | spl8_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f265,f257,f267,f98,f129])).
% 0.21/0.54  fof(f257,plain,(
% 0.21/0.54    spl8_16 <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.54  fof(f265,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl8_16),
% 0.21/0.54    inference(resolution,[],[f259,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f259,plain,(
% 0.21/0.54    ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) | spl8_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f257])).
% 0.21/0.54  fof(f264,plain,(
% 0.21/0.54    ~spl8_16 | spl8_17 | ~spl8_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f255,f243,f261,f257])).
% 0.21/0.54  fof(f255,plain,(
% 0.21/0.54    k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) | ~spl8_14),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f254])).
% 0.21/0.54  fof(f254,plain,(
% 0.21/0.54    k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0) | k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) | ~spl8_14),
% 0.21/0.54    inference(superposition,[],[f80,f245])).
% 0.21/0.54  fof(f245,plain,(
% 0.21/0.54    k1_funct_1(sK2,sK0) = sK7(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) | ~spl8_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f243])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sK7(X0,X1) != X0 | k1_enumset1(X0,X0,X0) = X1 | ~r2_hidden(sK7(X0,X1),X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f70,f74])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f250,plain,(
% 0.21/0.54    spl8_14 | spl8_15 | ~spl8_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f241,f236,f247,f243])).
% 0.21/0.54  fof(f236,plain,(
% 0.21/0.54    spl8_13 <=> ! [X0] : (k2_relat_1(sK2) != X0 | r2_hidden(sK7(k1_funct_1(sK2,sK0),X0),X0) | k1_funct_1(sK2,sK0) = sK7(k1_funct_1(sK2,sK0),X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.54  fof(f241,plain,(
% 0.21/0.54    r2_hidden(sK7(k1_funct_1(sK2,sK0),k2_relat_1(sK2)),k2_relat_1(sK2)) | k1_funct_1(sK2,sK0) = sK7(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) | ~spl8_13),
% 0.21/0.54    inference(equality_resolution,[],[f237])).
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    ( ! [X0] : (k2_relat_1(sK2) != X0 | r2_hidden(sK7(k1_funct_1(sK2,sK0),X0),X0) | k1_funct_1(sK2,sK0) = sK7(k1_funct_1(sK2,sK0),X0)) ) | ~spl8_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f236])).
% 0.21/0.54  fof(f238,plain,(
% 0.21/0.54    ~spl8_5 | spl8_13 | spl8_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f229,f123,f236,f118])).
% 0.21/0.54  fof(f229,plain,(
% 0.21/0.54    ( ! [X0] : (k2_relat_1(sK2) != X0 | k1_funct_1(sK2,sK0) = sK7(k1_funct_1(sK2,sK0),X0) | r2_hidden(sK7(k1_funct_1(sK2,sK0),X0),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))) ) | spl8_6),
% 0.21/0.54    inference(superposition,[],[f205,f53])).
% 0.21/0.54  fof(f205,plain,(
% 0.21/0.54    ( ! [X17] : (k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) != X17 | k1_funct_1(sK2,sK0) = sK7(k1_funct_1(sK2,sK0),X17) | r2_hidden(sK7(k1_funct_1(sK2,sK0),X17),X17)) ) | spl8_6),
% 0.21/0.54    inference(superposition,[],[f125,f81])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = X1 | sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f69,f74])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    spl8_7 | ~spl8_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f127,f118,f129])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    v1_relat_1(sK2) | ~spl8_5),
% 0.21/0.54    inference(resolution,[],[f66,f120])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    ~spl8_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f75,f123])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    k2_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK2) != k1_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 0.21/0.54    inference(definition_unfolding,[],[f46,f74,f74])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.21/0.54    inference(negated_conjecture,[],[f13])).
% 0.21/0.54  fof(f13,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    spl8_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f76,f118])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 0.21/0.54    inference(definition_unfolding,[],[f44,f74])).
% 0.21/0.54  % (23140)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    spl8_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f77,f113])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    v1_funct_2(sK2,k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.21/0.54    inference(definition_unfolding,[],[f43,f74])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ~spl8_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f45,f103])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    k1_xboole_0 != sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    spl8_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f42,f98])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (23147)------------------------------
% 0.21/0.54  % (23147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23147)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (23147)Memory used [KB]: 11129
% 0.21/0.54  % (23147)Time elapsed: 0.079 s
% 0.21/0.54  % (23147)------------------------------
% 0.21/0.54  % (23147)------------------------------
% 0.21/0.55  % (23142)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (23141)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (23140)Refutation not found, incomplete strategy% (23140)------------------------------
% 0.21/0.55  % (23140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (23140)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (23140)Memory used [KB]: 10618
% 0.21/0.55  % (23140)Time elapsed: 0.141 s
% 0.21/0.55  % (23140)------------------------------
% 0.21/0.55  % (23140)------------------------------
% 0.21/0.55  % (23119)Success in time 0.189 s
%------------------------------------------------------------------------------

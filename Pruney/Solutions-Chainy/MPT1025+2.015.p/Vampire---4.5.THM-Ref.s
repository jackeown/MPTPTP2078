%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 201 expanded)
%              Number of leaves         :   26 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  440 (1077 expanded)
%              Number of equality atoms :   66 ( 187 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f91,f95,f101,f119,f126,f128,f165,f177,f188,f192])).

fof(f192,plain,
    ( ~ spl11_4
    | ~ spl11_15 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_15 ),
    inference(resolution,[],[f189,f90])).

fof(f90,plain,
    ( r2_hidden(sK6,k9_relat_1(sK5,sK4))
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl11_4
  <=> r2_hidden(sK6,k9_relat_1(sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f189,plain,
    ( ~ r2_hidden(sK6,k9_relat_1(sK5,sK4))
    | ~ spl11_15 ),
    inference(equality_resolution,[],[f187])).

fof(f187,plain,
    ( ! [X0] :
        ( sK6 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK5,sK4)) )
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl11_15
  <=> ! [X0] :
        ( sK6 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK5,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f188,plain,
    ( ~ spl11_6
    | spl11_15
    | ~ spl11_13 ),
    inference(avatar_split_clause,[],[f184,f163,f186,f113])).

fof(f113,plain,
    ( spl11_6
  <=> sP1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f163,plain,
    ( spl11_13
  <=> ! [X1,X0] :
        ( sK6 != X0
        | ~ sP0(sK5,sK4,X1)
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k9_relat_1(sK5,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f184,plain,
    ( ! [X0] :
        ( sK6 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK5,sK4))
        | ~ sP1(sK5) )
    | ~ spl11_13 ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( ! [X0] :
        ( sK6 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK5,sK4))
        | ~ r2_hidden(X0,k9_relat_1(sK5,sK4))
        | ~ sP1(sK5) )
    | ~ spl11_13 ),
    inference(resolution,[],[f164,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1,k9_relat_1(X0,X1))
      | ~ sP1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ~ sP0(X0,X1,X2) )
          & ( sP0(X0,X1,X2)
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> sP0(X0,X1,X2) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( ~ sP0(sK5,sK4,X1)
        | sK6 != X0
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k9_relat_1(sK5,sK4)) )
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f163])).

fof(f177,plain,(
    spl11_12 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl11_12 ),
    inference(resolution,[],[f166,f40])).

fof(f40,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ! [X5] :
        ( k1_funct_1(sK5,X5) != sK6
        | ~ r2_hidden(X5,sK4)
        | ~ m1_subset_1(X5,sK2) )
    & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f11,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK5,X5) != X4
              | ~ r2_hidden(X5,sK4)
              | ~ m1_subset_1(X5,sK2) )
          & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK5,sK2,sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK5,X5) != X4
            | ~ r2_hidden(X5,sK4)
            | ~ m1_subset_1(X5,sK2) )
        & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4)) )
   => ( ! [X5] :
          ( k1_funct_1(sK5,X5) != sK6
          | ~ r2_hidden(X5,sK4)
          | ~ m1_subset_1(X5,sK2) )
      & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f166,plain,
    ( ! [X0] : ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | spl11_12 ),
    inference(resolution,[],[f161,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f161,plain,
    ( ~ v4_relat_1(sK5,sK2)
    | spl11_12 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl11_12
  <=> v4_relat_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f165,plain,
    ( ~ spl11_1
    | ~ spl11_12
    | spl11_13
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f156,f117,f163,f159,f69])).

fof(f69,plain,
    ( spl11_1
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f117,plain,
    ( spl11_7
  <=> ! [X1,X0] :
        ( sK6 != X0
        | ~ r1_tarski(X1,sK2)
        | ~ r2_hidden(sK9(sK5,sK4,X0),X1)
        | ~ r2_hidden(X0,k9_relat_1(sK5,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( sK6 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK5,sK4))
        | ~ v4_relat_1(sK5,sK2)
        | ~ v1_relat_1(sK5)
        | ~ r2_hidden(X0,X1)
        | ~ sP0(sK5,sK4,X1) )
    | ~ spl11_7 ),
    inference(resolution,[],[f132,f45])).

fof(f45,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != sK7(X0,X1,X2)
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( sK7(X0,X1,X2) = k1_funct_1(X0,sK8(X0,X1,X2))
              & r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( k1_funct_1(X0,X7) != X6
                  | ~ r2_hidden(X7,X1)
                  | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
            & ( ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
                & r2_hidden(sK9(X0,X1,X6),X1)
                & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f28,f31,f30,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK7(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK7(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK7(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK7(X0,X1,X2) = k1_funct_1(X0,sK8(X0,X1,X2))
        & r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK9(X0,X1,X6)) = X6
        & r2_hidden(sK9(X0,X1,X6),X1)
        & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( k1_funct_1(X0,X4) != X3
                  | ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( k1_funct_1(X0,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X5,k1_relat_1(X0)) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( k1_funct_1(X0,X7) != X6
                  | ~ r2_hidden(X7,X1)
                  | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
            & ( ? [X8] :
                  ( k1_funct_1(X0,X8) = X6
                  & r2_hidden(X8,X1)
                  & r2_hidden(X8,k1_relat_1(X0)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( k1_funct_1(X0,X4) != X3
                  | ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( k1_funct_1(X0,X4) != X3
                  | ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
            & ( ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( k1_funct_1(X0,X4) = X3
              & r2_hidden(X4,X1)
              & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f132,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK9(sK5,sK4,X2),k1_relat_1(X3))
        | sK6 != X2
        | ~ r2_hidden(X2,k9_relat_1(sK5,sK4))
        | ~ v4_relat_1(X3,sK2)
        | ~ v1_relat_1(X3) )
    | ~ spl11_7 ),
    inference(resolution,[],[f118,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f118,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,sK2)
        | sK6 != X0
        | ~ r2_hidden(sK9(sK5,sK4,X0),X1)
        | ~ r2_hidden(X0,k9_relat_1(sK5,sK4)) )
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f128,plain,(
    spl11_8 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl11_8 ),
    inference(resolution,[],[f125,f38])).

fof(f38,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f125,plain,
    ( ~ v1_funct_1(sK5)
    | spl11_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl11_8
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f126,plain,
    ( ~ spl11_1
    | ~ spl11_8
    | spl11_6 ),
    inference(avatar_split_clause,[],[f121,f113,f123,f69])).

fof(f121,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl11_6 ),
    inference(resolution,[],[f115,f53])).

fof(f53,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f13,f21,f20])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f115,plain,
    ( ~ sP1(sK5)
    | spl11_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f119,plain,
    ( ~ spl11_6
    | spl11_7
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f111,f99,f117,f113])).

fof(f99,plain,
    ( spl11_5
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK5,X1))
        | k1_funct_1(sK5,sK9(sK5,X1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( sK6 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK5,sK4))
        | ~ r2_hidden(sK9(sK5,sK4,X0),X1)
        | ~ r1_tarski(X1,sK2)
        | ~ sP1(sK5) )
    | ~ spl11_5 ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( sK6 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK5,sK4))
        | ~ r2_hidden(X0,k9_relat_1(sK5,sK4))
        | ~ r2_hidden(sK9(sK5,sK4,X0),X1)
        | ~ r1_tarski(X1,sK2)
        | ~ sP1(sK5) )
    | ~ spl11_5 ),
    inference(resolution,[],[f107,f64])).

fof(f107,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP0(sK5,sK4,X1)
        | sK6 != X0
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k9_relat_1(sK5,sK4))
        | ~ r2_hidden(sK9(sK5,sK4,X0),X2)
        | ~ r1_tarski(X2,sK2) )
    | ~ spl11_5 ),
    inference(resolution,[],[f105,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK10(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

% (25286)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

% (25294)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f105,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK9(sK5,sK4,X0),sK2)
        | ~ r2_hidden(X0,k9_relat_1(sK5,sK4))
        | sK6 != X0
        | ~ r2_hidden(X0,X1)
        | ~ sP0(sK5,sK4,X1) )
    | ~ spl11_5 ),
    inference(resolution,[],[f104,f46])).

fof(f46,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK9(sK5,X0,X1),sK4)
        | sK6 != X1
        | ~ r2_hidden(X1,k9_relat_1(sK5,X0))
        | ~ r2_hidden(sK9(sK5,X0,X1),sK2) )
    | ~ spl11_5 ),
    inference(resolution,[],[f102,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK9(sK5,X0,X1),sK2)
        | ~ r2_hidden(sK9(sK5,X0,X1),sK4)
        | sK6 != X1
        | ~ r2_hidden(X1,k9_relat_1(sK5,X0)) )
    | ~ spl11_5 ),
    inference(superposition,[],[f42,f100])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK5,sK9(sK5,X1,X0)) = X0
        | ~ r2_hidden(X0,k9_relat_1(sK5,X1)) )
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f42,plain,(
    ! [X5] :
      ( k1_funct_1(sK5,X5) != sK6
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f101,plain,
    ( ~ spl11_1
    | spl11_5 ),
    inference(avatar_split_clause,[],[f97,f99,f69])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK5,X1))
      | k1_funct_1(sK5,sK9(sK5,X1,X0)) = X0
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f96,f38])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X2,k9_relat_1(X0,X1))
      | k1_funct_1(X0,sK9(X0,X1,X2)) = X2
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f81,f53])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X1)
      | k1_funct_1(X1,sK9(X1,X2,X0)) = X0
      | ~ r2_hidden(X0,k9_relat_1(X1,X2)) ) ),
    inference(resolution,[],[f47,f64])).

fof(f47,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X6,X2)
      | k1_funct_1(X0,sK9(X0,X1,X6)) = X6 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f95,plain,(
    spl11_3 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl11_3 ),
    inference(resolution,[],[f86,f40])).

fof(f86,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | spl11_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl11_3
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f91,plain,
    ( ~ spl11_3
    | spl11_4 ),
    inference(avatar_split_clause,[],[f82,f88,f84])).

fof(f82,plain,
    ( r2_hidden(sK6,k9_relat_1(sK5,sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(superposition,[],[f41,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f41,plain,(
    r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl11_1 ),
    inference(resolution,[],[f76,f40])).

fof(f76,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl11_1 ),
    inference(resolution,[],[f71,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f71,plain,
    ( ~ v1_relat_1(sK5)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (25296)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (25306)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (25298)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (25312)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (25288)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (25290)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (25296)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (25304)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f79,f91,f95,f101,f119,f126,f128,f165,f177,f188,f192])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    ~spl11_4 | ~spl11_15),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    $false | (~spl11_4 | ~spl11_15)),
% 0.21/0.52    inference(resolution,[],[f189,f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    r2_hidden(sK6,k9_relat_1(sK5,sK4)) | ~spl11_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl11_4 <=> r2_hidden(sK6,k9_relat_1(sK5,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    ~r2_hidden(sK6,k9_relat_1(sK5,sK4)) | ~spl11_15),
% 0.21/0.52    inference(equality_resolution,[],[f187])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    ( ! [X0] : (sK6 != X0 | ~r2_hidden(X0,k9_relat_1(sK5,sK4))) ) | ~spl11_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f186])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    spl11_15 <=> ! [X0] : (sK6 != X0 | ~r2_hidden(X0,k9_relat_1(sK5,sK4)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    ~spl11_6 | spl11_15 | ~spl11_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f184,f163,f186,f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl11_6 <=> sP1(sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    spl11_13 <=> ! [X1,X0] : (sK6 != X0 | ~sP0(sK5,sK4,X1) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k9_relat_1(sK5,sK4)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    ( ! [X0] : (sK6 != X0 | ~r2_hidden(X0,k9_relat_1(sK5,sK4)) | ~sP1(sK5)) ) | ~spl11_13),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f183])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    ( ! [X0] : (sK6 != X0 | ~r2_hidden(X0,k9_relat_1(sK5,sK4)) | ~r2_hidden(X0,k9_relat_1(sK5,sK4)) | ~sP1(sK5)) ) | ~spl11_13),
% 0.21/0.52    inference(resolution,[],[f164,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP0(X0,X1,k9_relat_1(X0,X1)) | ~sP1(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | k9_relat_1(X0,X1) != X2 | ~sP1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ~sP0(X0,X1,X2)) & (sP0(X0,X1,X2) | k9_relat_1(X0,X1) != X2)) | ~sP1(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> sP0(X0,X1,X2)) | ~sP1(X0))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sP0(sK5,sK4,X1) | sK6 != X0 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k9_relat_1(sK5,sK4))) ) | ~spl11_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f163])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    spl11_12),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f175])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    $false | spl11_12),
% 0.21/0.52    inference(resolution,[],[f166,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    (! [X5] : (k1_funct_1(sK5,X5) != sK6 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,sK2)) & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f11,f24,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK5,X5) != X4 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,sK2)) & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X4] : (! [X5] : (k1_funct_1(sK5,X5) != X4 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,sK2)) & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4))) => (! [X5] : (k1_funct_1(sK5,X5) != sK6 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,sK2)) & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.52    inference(negated_conjecture,[],[f8])).
% 0.21/0.52  fof(f8,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | spl11_12),
% 0.21/0.52    inference(resolution,[],[f161,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ~v4_relat_1(sK5,sK2) | spl11_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f159])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    spl11_12 <=> v4_relat_1(sK5,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ~spl11_1 | ~spl11_12 | spl11_13 | ~spl11_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f156,f117,f163,f159,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl11_1 <=> v1_relat_1(sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    spl11_7 <=> ! [X1,X0] : (sK6 != X0 | ~r1_tarski(X1,sK2) | ~r2_hidden(sK9(sK5,sK4,X0),X1) | ~r2_hidden(X0,k9_relat_1(sK5,sK4)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK6 != X0 | ~r2_hidden(X0,k9_relat_1(sK5,sK4)) | ~v4_relat_1(sK5,sK2) | ~v1_relat_1(sK5) | ~r2_hidden(X0,X1) | ~sP0(sK5,sK4,X1)) ) | ~spl11_7),
% 0.21/0.52    inference(resolution,[],[f132,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X6,X2,X0,X1] : (r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (k1_funct_1(X0,X4) != sK7(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((sK7(X0,X1,X2) = k1_funct_1(X0,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK9(X0,X1,X6)) = X6 & r2_hidden(sK9(X0,X1,X6),X1) & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f28,f31,f30,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK7(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK7(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK7(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK7(X0,X1,X2) = k1_funct_1(X0,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK9(X0,X1,X6)) = X6 & r2_hidden(sK9(X0,X1,X6),X1) & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.52    inference(rectify,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.52    inference(nnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (sP0(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0)))))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(sK9(sK5,sK4,X2),k1_relat_1(X3)) | sK6 != X2 | ~r2_hidden(X2,k9_relat_1(sK5,sK4)) | ~v4_relat_1(X3,sK2) | ~v1_relat_1(X3)) ) | ~spl11_7),
% 0.21/0.52    inference(resolution,[],[f118,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,sK2) | sK6 != X0 | ~r2_hidden(sK9(sK5,sK4,X0),X1) | ~r2_hidden(X0,k9_relat_1(sK5,sK4))) ) | ~spl11_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f117])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    spl11_8),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f127])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    $false | spl11_8),
% 0.21/0.52    inference(resolution,[],[f125,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    v1_funct_1(sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 1.37/0.53  fof(f125,plain,(
% 1.37/0.53    ~v1_funct_1(sK5) | spl11_8),
% 1.37/0.53    inference(avatar_component_clause,[],[f123])).
% 1.37/0.53  fof(f123,plain,(
% 1.37/0.53    spl11_8 <=> v1_funct_1(sK5)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 1.37/0.53  fof(f126,plain,(
% 1.37/0.53    ~spl11_1 | ~spl11_8 | spl11_6),
% 1.37/0.53    inference(avatar_split_clause,[],[f121,f113,f123,f69])).
% 1.37/0.53  fof(f121,plain,(
% 1.37/0.53    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | spl11_6),
% 1.37/0.53    inference(resolution,[],[f115,f53])).
% 1.37/0.53  fof(f53,plain,(
% 1.37/0.53    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f22])).
% 1.37/0.53  fof(f22,plain,(
% 1.37/0.53    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.37/0.53    inference(definition_folding,[],[f13,f21,f20])).
% 1.37/0.53  fof(f13,plain,(
% 1.37/0.53    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.37/0.53    inference(flattening,[],[f12])).
% 1.37/0.53  fof(f12,plain,(
% 1.37/0.53    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.37/0.53    inference(ennf_transformation,[],[f4])).
% 1.37/0.53  fof(f4,axiom,(
% 1.37/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).
% 1.37/0.53  fof(f115,plain,(
% 1.37/0.53    ~sP1(sK5) | spl11_6),
% 1.37/0.53    inference(avatar_component_clause,[],[f113])).
% 1.37/0.53  fof(f119,plain,(
% 1.37/0.53    ~spl11_6 | spl11_7 | ~spl11_5),
% 1.37/0.53    inference(avatar_split_clause,[],[f111,f99,f117,f113])).
% 1.37/0.53  fof(f99,plain,(
% 1.37/0.53    spl11_5 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(sK5,X1)) | k1_funct_1(sK5,sK9(sK5,X1,X0)) = X0)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.37/0.53  fof(f111,plain,(
% 1.37/0.53    ( ! [X0,X1] : (sK6 != X0 | ~r2_hidden(X0,k9_relat_1(sK5,sK4)) | ~r2_hidden(sK9(sK5,sK4,X0),X1) | ~r1_tarski(X1,sK2) | ~sP1(sK5)) ) | ~spl11_5),
% 1.37/0.53    inference(duplicate_literal_removal,[],[f110])).
% 1.37/0.53  fof(f110,plain,(
% 1.37/0.53    ( ! [X0,X1] : (sK6 != X0 | ~r2_hidden(X0,k9_relat_1(sK5,sK4)) | ~r2_hidden(X0,k9_relat_1(sK5,sK4)) | ~r2_hidden(sK9(sK5,sK4,X0),X1) | ~r1_tarski(X1,sK2) | ~sP1(sK5)) ) | ~spl11_5),
% 1.37/0.53    inference(resolution,[],[f107,f64])).
% 1.37/0.53  fof(f107,plain,(
% 1.37/0.53    ( ! [X2,X0,X1] : (~sP0(sK5,sK4,X1) | sK6 != X0 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k9_relat_1(sK5,sK4)) | ~r2_hidden(sK9(sK5,sK4,X0),X2) | ~r1_tarski(X2,sK2)) ) | ~spl11_5),
% 1.37/0.53    inference(resolution,[],[f105,f57])).
% 1.37/0.53  fof(f57,plain,(
% 1.37/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f37])).
% 1.37/0.53  fof(f37,plain,(
% 1.37/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.37/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f35,f36])).
% 1.37/0.53  fof(f36,plain,(
% 1.37/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0)))),
% 1.37/0.53    introduced(choice_axiom,[])).
% 1.37/0.53  fof(f35,plain,(
% 1.37/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.37/0.53    inference(rectify,[],[f34])).
% 1.37/0.53  % (25286)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.53  fof(f34,plain,(
% 1.37/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.37/0.53    inference(nnf_transformation,[],[f16])).
% 1.37/0.53  fof(f16,plain,(
% 1.37/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.37/0.53    inference(ennf_transformation,[],[f1])).
% 1.37/0.53  % (25294)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.53  fof(f1,axiom,(
% 1.37/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.37/0.53  fof(f105,plain,(
% 1.37/0.53    ( ! [X0,X1] : (~r2_hidden(sK9(sK5,sK4,X0),sK2) | ~r2_hidden(X0,k9_relat_1(sK5,sK4)) | sK6 != X0 | ~r2_hidden(X0,X1) | ~sP0(sK5,sK4,X1)) ) | ~spl11_5),
% 1.37/0.53    inference(resolution,[],[f104,f46])).
% 1.37/0.53  fof(f46,plain,(
% 1.37/0.53    ( ! [X6,X2,X0,X1] : (r2_hidden(sK9(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f32])).
% 1.37/0.53  fof(f104,plain,(
% 1.37/0.53    ( ! [X0,X1] : (~r2_hidden(sK9(sK5,X0,X1),sK4) | sK6 != X1 | ~r2_hidden(X1,k9_relat_1(sK5,X0)) | ~r2_hidden(sK9(sK5,X0,X1),sK2)) ) | ~spl11_5),
% 1.37/0.53    inference(resolution,[],[f102,f56])).
% 1.37/0.53  fof(f56,plain,(
% 1.37/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f15])).
% 1.37/0.53  fof(f15,plain,(
% 1.37/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.37/0.53    inference(ennf_transformation,[],[f2])).
% 1.37/0.53  fof(f2,axiom,(
% 1.37/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.37/0.53  fof(f102,plain,(
% 1.37/0.53    ( ! [X0,X1] : (~m1_subset_1(sK9(sK5,X0,X1),sK2) | ~r2_hidden(sK9(sK5,X0,X1),sK4) | sK6 != X1 | ~r2_hidden(X1,k9_relat_1(sK5,X0))) ) | ~spl11_5),
% 1.37/0.53    inference(superposition,[],[f42,f100])).
% 1.37/0.53  fof(f100,plain,(
% 1.37/0.53    ( ! [X0,X1] : (k1_funct_1(sK5,sK9(sK5,X1,X0)) = X0 | ~r2_hidden(X0,k9_relat_1(sK5,X1))) ) | ~spl11_5),
% 1.37/0.53    inference(avatar_component_clause,[],[f99])).
% 1.37/0.53  fof(f42,plain,(
% 1.37/0.53    ( ! [X5] : (k1_funct_1(sK5,X5) != sK6 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,sK2)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f25])).
% 1.37/0.53  fof(f101,plain,(
% 1.37/0.53    ~spl11_1 | spl11_5),
% 1.37/0.53    inference(avatar_split_clause,[],[f97,f99,f69])).
% 1.37/0.53  fof(f97,plain,(
% 1.37/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK5,X1)) | k1_funct_1(sK5,sK9(sK5,X1,X0)) = X0 | ~v1_relat_1(sK5)) )),
% 1.37/0.53    inference(resolution,[],[f96,f38])).
% 1.37/0.53  fof(f96,plain,(
% 1.37/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(X2,k9_relat_1(X0,X1)) | k1_funct_1(X0,sK9(X0,X1,X2)) = X2 | ~v1_relat_1(X0)) )),
% 1.37/0.53    inference(resolution,[],[f81,f53])).
% 1.37/0.53  fof(f81,plain,(
% 1.37/0.53    ( ! [X2,X0,X1] : (~sP1(X1) | k1_funct_1(X1,sK9(X1,X2,X0)) = X0 | ~r2_hidden(X0,k9_relat_1(X1,X2))) )),
% 1.37/0.53    inference(resolution,[],[f47,f64])).
% 1.37/0.53  fof(f47,plain,(
% 1.37/0.53    ( ! [X6,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X6,X2) | k1_funct_1(X0,sK9(X0,X1,X6)) = X6) )),
% 1.37/0.53    inference(cnf_transformation,[],[f32])).
% 1.37/0.53  fof(f95,plain,(
% 1.37/0.53    spl11_3),
% 1.37/0.53    inference(avatar_contradiction_clause,[],[f93])).
% 1.37/0.53  fof(f93,plain,(
% 1.37/0.53    $false | spl11_3),
% 1.37/0.53    inference(resolution,[],[f86,f40])).
% 1.37/0.53  fof(f86,plain,(
% 1.37/0.53    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | spl11_3),
% 1.37/0.53    inference(avatar_component_clause,[],[f84])).
% 1.37/0.53  fof(f84,plain,(
% 1.37/0.53    spl11_3 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.37/0.53  fof(f91,plain,(
% 1.37/0.53    ~spl11_3 | spl11_4),
% 1.37/0.53    inference(avatar_split_clause,[],[f82,f88,f84])).
% 1.37/0.53  fof(f82,plain,(
% 1.37/0.53    r2_hidden(sK6,k9_relat_1(sK5,sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 1.37/0.53    inference(superposition,[],[f41,f63])).
% 1.37/0.53  fof(f63,plain,(
% 1.37/0.53    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.37/0.53    inference(cnf_transformation,[],[f19])).
% 1.37/0.53  fof(f19,plain,(
% 1.37/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.53    inference(ennf_transformation,[],[f7])).
% 1.37/0.53  fof(f7,axiom,(
% 1.37/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.37/0.53  fof(f41,plain,(
% 1.37/0.53    r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))),
% 1.37/0.53    inference(cnf_transformation,[],[f25])).
% 1.37/0.53  fof(f79,plain,(
% 1.37/0.53    spl11_1),
% 1.37/0.53    inference(avatar_contradiction_clause,[],[f77])).
% 1.37/0.53  fof(f77,plain,(
% 1.37/0.53    $false | spl11_1),
% 1.37/0.53    inference(resolution,[],[f76,f40])).
% 1.37/0.53  fof(f76,plain,(
% 1.37/0.53    ( ! [X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl11_1),
% 1.37/0.53    inference(resolution,[],[f71,f60])).
% 1.37/0.53  fof(f60,plain,(
% 1.37/0.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.37/0.53    inference(cnf_transformation,[],[f17])).
% 1.37/0.53  fof(f17,plain,(
% 1.37/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.53    inference(ennf_transformation,[],[f5])).
% 1.37/0.53  fof(f5,axiom,(
% 1.37/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.37/0.53  fof(f71,plain,(
% 1.37/0.53    ~v1_relat_1(sK5) | spl11_1),
% 1.37/0.53    inference(avatar_component_clause,[],[f69])).
% 1.37/0.53  % SZS output end Proof for theBenchmark
% 1.37/0.53  % (25296)------------------------------
% 1.37/0.53  % (25296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (25296)Termination reason: Refutation
% 1.37/0.53  
% 1.37/0.53  % (25296)Memory used [KB]: 6268
% 1.37/0.53  % (25296)Time elapsed: 0.102 s
% 1.37/0.53  % (25296)------------------------------
% 1.37/0.53  % (25296)------------------------------
% 1.37/0.53  % (25289)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.37/0.53  % (25310)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.37/0.53  % (25283)Success in time 0.176 s
%------------------------------------------------------------------------------

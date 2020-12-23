%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 186 expanded)
%              Number of leaves         :   26 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  351 ( 815 expanded)
%              Number of equality atoms :   55 ( 139 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f144,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f76,f82,f95,f104,f118,f128,f133,f140,f143])).

fof(f143,plain,
    ( ~ spl10_5
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_11 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl10_5
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f141,f120])).

fof(f120,plain,
    ( sK6 = k1_funct_1(sK5,sK9(sK5,sK4,sK6))
    | ~ spl10_5
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f83,f117,f42])).

fof(f42,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X6,X2)
      | k1_funct_1(X0,sK9(X0,X1,X6)) = X6 ) ),
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

fof(f117,plain,
    ( r2_hidden(sK6,k9_relat_1(sK5,sK4))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl10_8
  <=> r2_hidden(sK6,k9_relat_1(sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f83,plain,
    ( ! [X0] : sP0(sK5,X0,k9_relat_1(sK5,X0))
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f81,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1,k9_relat_1(X0,X1))
      | ~ sP1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
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

fof(f81,plain,
    ( sP1(sK5)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl10_5
  <=> sP1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f141,plain,
    ( sK6 != k1_funct_1(sK5,sK9(sK5,sK4,sK6))
    | ~ spl10_9
    | ~ spl10_11 ),
    inference(unit_resulting_resolution,[],[f127,f139,f36])).

fof(f36,plain,(
    ! [X5] :
      ( k1_funct_1(sK5,X5) != sK6
      | ~ r2_hidden(X5,sK4)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ! [X5] :
        ( k1_funct_1(sK5,X5) != sK6
        | ~ r2_hidden(X5,sK4)
        | ~ r2_hidden(X5,sK2) )
    & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f12,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK5,X5) != X4
              | ~ r2_hidden(X5,sK4)
              | ~ r2_hidden(X5,sK2) )
          & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK5,X5) != X4
            | ~ r2_hidden(X5,sK4)
            | ~ r2_hidden(X5,sK2) )
        & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4)) )
   => ( ! [X5] :
          ( k1_funct_1(sK5,X5) != sK6
          | ~ r2_hidden(X5,sK4)
          | ~ r2_hidden(X5,sK2) )
      & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

fof(f139,plain,
    ( r2_hidden(sK9(sK5,sK4,sK6),sK2)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl10_11
  <=> r2_hidden(sK9(sK5,sK4,sK6),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f127,plain,
    ( r2_hidden(sK9(sK5,sK4,sK6),sK4)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl10_9
  <=> r2_hidden(sK9(sK5,sK4,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f140,plain,
    ( spl10_11
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f134,f130,f101,f137])).

fof(f101,plain,
    ( spl10_7
  <=> m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f130,plain,
    ( spl10_10
  <=> r2_hidden(sK9(sK5,sK4,sK6),k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f134,plain,
    ( r2_hidden(sK9(sK5,sK4,sK6),sK2)
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f103,f132,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f132,plain,
    ( r2_hidden(sK9(sK5,sK4,sK6),k1_relat_1(sK5))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f103,plain,
    ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f133,plain,
    ( spl10_10
    | ~ spl10_5
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f121,f115,f79,f130])).

fof(f121,plain,
    ( r2_hidden(sK9(sK5,sK4,sK6),k1_relat_1(sK5))
    | ~ spl10_5
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f83,f117,f40])).

fof(f40,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f128,plain,
    ( spl10_9
    | ~ spl10_5
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f122,f115,f79,f125])).

fof(f122,plain,
    ( r2_hidden(sK9(sK5,sK4,sK6),sK4)
    | ~ spl10_5
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f83,f117,f41])).

fof(f41,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f118,plain,
    ( spl10_8
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f113,f67,f62,f115])).

fof(f62,plain,
    ( spl10_2
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f67,plain,
    ( spl10_3
  <=> r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f113,plain,
    ( r2_hidden(sK6,k9_relat_1(sK5,sK4))
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(backward_demodulation,[],[f69,f111])).

fof(f111,plain,
    ( ! [X0] : k9_relat_1(sK5,X0) = k7_relset_1(sK2,sK3,sK5,X0)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f64,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
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

fof(f64,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f69,plain,
    ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f104,plain,
    ( spl10_7
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f98,f92,f62,f101])).

fof(f92,plain,
    ( spl10_6
  <=> k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f98,plain,
    ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2))
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(forward_demodulation,[],[f96,f94])).

fof(f94,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f96,plain,
    ( m1_subset_1(k1_relset_1(sK2,sK3,sK5),k1_zfmisc_1(sK2))
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f64,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f95,plain,
    ( spl10_6
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f90,f62,f92])).

fof(f90,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f64,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f82,plain,
    ( spl10_5
    | ~ spl10_1
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f77,f73,f57,f79])).

fof(f57,plain,
    ( spl10_1
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f73,plain,
    ( spl10_4
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f77,plain,
    ( sP1(sK5)
    | ~ spl10_1
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f59,f75,f48])).

fof(f48,plain,(
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
    inference(definition_folding,[],[f15,f21,f20])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f75,plain,
    ( v1_relat_1(sK5)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f59,plain,
    ( v1_funct_1(sK5)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f76,plain,
    ( spl10_4
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f71,f62,f73])).

fof(f71,plain,
    ( v1_relat_1(sK5)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f49,f64,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f70,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f35,f67])).

fof(f35,plain,(
    r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f34,f62])).

fof(f34,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f33,f57])).

fof(f33,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (1834)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (1834)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f60,f65,f70,f76,f82,f95,f104,f118,f128,f133,f140,f143])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    ~spl10_5 | ~spl10_8 | ~spl10_9 | ~spl10_11),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f142])).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    $false | (~spl10_5 | ~spl10_8 | ~spl10_9 | ~spl10_11)),
% 0.20/0.47    inference(subsumption_resolution,[],[f141,f120])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    sK6 = k1_funct_1(sK5,sK9(sK5,sK4,sK6)) | (~spl10_5 | ~spl10_8)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f83,f117,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X6,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X6,X2) | k1_funct_1(X0,sK9(X0,X1,X6)) = X6) )),
% 0.20/0.47    inference(cnf_transformation,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (k1_funct_1(X0,X4) != sK7(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((sK7(X0,X1,X2) = k1_funct_1(X0,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK9(X0,X1,X6)) = X6 & r2_hidden(sK9(X0,X1,X6),X1) & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f28,f31,f30,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK7(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK7(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK7(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK7(X0,X1,X2) = k1_funct_1(X0,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK9(X0,X1,X6)) = X6 & r2_hidden(sK9(X0,X1,X6),X1) & r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.47    inference(rectify,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.47    inference(nnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (sP0(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0)))))),
% 0.20/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    r2_hidden(sK6,k9_relat_1(sK5,sK4)) | ~spl10_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f115])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    spl10_8 <=> r2_hidden(sK6,k9_relat_1(sK5,sK4))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    ( ! [X0] : (sP0(sK5,X0,k9_relat_1(sK5,X0))) ) | ~spl10_5),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f81,f54])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X0,X1] : (sP0(X0,X1,k9_relat_1(X0,X1)) | ~sP1(X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | k9_relat_1(X0,X1) != X2 | ~sP1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ~sP0(X0,X1,X2)) & (sP0(X0,X1,X2) | k9_relat_1(X0,X1) != X2)) | ~sP1(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> sP0(X0,X1,X2)) | ~sP1(X0))),
% 0.20/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    sP1(sK5) | ~spl10_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f79])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    spl10_5 <=> sP1(sK5)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    sK6 != k1_funct_1(sK5,sK9(sK5,sK4,sK6)) | (~spl10_9 | ~spl10_11)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f127,f139,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X5] : (k1_funct_1(sK5,X5) != sK6 | ~r2_hidden(X5,sK4) | ~r2_hidden(X5,sK2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    (! [X5] : (k1_funct_1(sK5,X5) != sK6 | ~r2_hidden(X5,sK4) | ~r2_hidden(X5,sK2)) & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK5)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f12,f24,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK5,X5) != X4 | ~r2_hidden(X5,sK4) | ~r2_hidden(X5,sK2)) & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK5))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ? [X4] : (! [X5] : (k1_funct_1(sK5,X5) != X4 | ~r2_hidden(X5,sK4) | ~r2_hidden(X5,sK2)) & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4))) => (! [X5] : (k1_funct_1(sK5,X5) != sK6 | ~r2_hidden(X5,sK4) | ~r2_hidden(X5,sK2)) & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.20/0.47    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.47  fof(f9,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.20/0.47    inference(negated_conjecture,[],[f8])).
% 0.20/0.47  fof(f8,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    r2_hidden(sK9(sK5,sK4,sK6),sK2) | ~spl10_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f137])).
% 0.20/0.47  fof(f137,plain,(
% 0.20/0.47    spl10_11 <=> r2_hidden(sK9(sK5,sK4,sK6),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    r2_hidden(sK9(sK5,sK4,sK6),sK4) | ~spl10_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f125])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    spl10_9 <=> r2_hidden(sK9(sK5,sK4,sK6),sK4)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    spl10_11 | ~spl10_7 | ~spl10_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f134,f130,f101,f137])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    spl10_7 <=> m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    spl10_10 <=> r2_hidden(sK9(sK5,sK4,sK6),k1_relat_1(sK5))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    r2_hidden(sK9(sK5,sK4,sK6),sK2) | (~spl10_7 | ~spl10_10)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f103,f132,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    r2_hidden(sK9(sK5,sK4,sK6),k1_relat_1(sK5)) | ~spl10_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f130])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2)) | ~spl10_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f101])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    spl10_10 | ~spl10_5 | ~spl10_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f121,f115,f79,f130])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    r2_hidden(sK9(sK5,sK4,sK6),k1_relat_1(sK5)) | (~spl10_5 | ~spl10_8)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f83,f117,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X6,X2,X0,X1] : (r2_hidden(sK9(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f32])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    spl10_9 | ~spl10_5 | ~spl10_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f122,f115,f79,f125])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    r2_hidden(sK9(sK5,sK4,sK6),sK4) | (~spl10_5 | ~spl10_8)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f83,f117,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X6,X2,X0,X1] : (r2_hidden(sK9(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f32])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    spl10_8 | ~spl10_2 | ~spl10_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f113,f67,f62,f115])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl10_2 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    spl10_3 <=> r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    r2_hidden(sK6,k9_relat_1(sK5,sK4)) | (~spl10_2 | ~spl10_3)),
% 0.20/0.47    inference(backward_demodulation,[],[f69,f111])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ( ! [X0] : (k9_relat_1(sK5,X0) = k7_relset_1(sK2,sK3,sK5,X0)) ) | ~spl10_2),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f64,f53])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~spl10_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f62])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) | ~spl10_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f67])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    spl10_7 | ~spl10_2 | ~spl10_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f98,f92,f62,f101])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    spl10_6 <=> k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2)) | (~spl10_2 | ~spl10_6)),
% 0.20/0.47    inference(forward_demodulation,[],[f96,f94])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) | ~spl10_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f92])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    m1_subset_1(k1_relset_1(sK2,sK3,sK5),k1_zfmisc_1(sK2)) | ~spl10_2),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f64,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    spl10_6 | ~spl10_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f90,f62,f92])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) | ~spl10_2),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f64,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl10_5 | ~spl10_1 | ~spl10_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f77,f73,f57,f79])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    spl10_1 <=> v1_funct_1(sK5)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    spl10_4 <=> v1_relat_1(sK5)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    sP1(sK5) | (~spl10_1 | ~spl10_4)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f59,f75,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(definition_folding,[],[f15,f21,f20])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    v1_relat_1(sK5) | ~spl10_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f73])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    v1_funct_1(sK5) | ~spl10_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f57])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    spl10_4 | ~spl10_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f71,f62,f73])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    v1_relat_1(sK5) | ~spl10_2),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f49,f64,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    spl10_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f35,f67])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    spl10_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f34,f62])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    spl10_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f33,f57])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    v1_funct_1(sK5)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (1834)------------------------------
% 0.20/0.47  % (1834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (1834)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (1834)Memory used [KB]: 1663
% 0.20/0.47  % (1834)Time elapsed: 0.066 s
% 0.20/0.47  % (1834)------------------------------
% 0.20/0.47  % (1834)------------------------------
% 0.20/0.48  % (1825)Success in time 0.12 s
%------------------------------------------------------------------------------

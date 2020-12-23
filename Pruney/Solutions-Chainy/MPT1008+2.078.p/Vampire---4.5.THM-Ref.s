%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 267 expanded)
%              Number of leaves         :   26 ( 103 expanded)
%              Depth                    :   14
%              Number of atoms          :  399 ( 738 expanded)
%              Number of equality atoms :  125 ( 273 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f426,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f83,f90,f100,f105,f160,f173,f188,f205,f218,f223,f231,f311,f390,f409,f423])).

fof(f423,plain,
    ( ~ spl7_15
    | ~ spl7_30 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | ~ spl7_15
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f187,f408])).

fof(f408,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK2))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl7_30
  <=> ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f187,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl7_15
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f409,plain,
    ( ~ spl7_5
    | ~ spl7_1
    | spl7_30
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f405,f388,f407,f70,f97])).

fof(f97,plain,
    ( spl7_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f70,plain,
    ( spl7_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f388,plain,
    ( spl7_29
  <=> ! [X1,X0] :
        ( k1_funct_1(sK2,X1) != X0
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f405,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_29 ),
    inference(duplicate_literal_removal,[],[f397])).

fof(f397,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl7_29 ),
    inference(resolution,[],[f395,f58])).

fof(f58,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f395,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl7_29 ),
    inference(equality_resolution,[],[f389])).

fof(f389,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK2,X1) != X0
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f388])).

fof(f390,plain,
    ( ~ spl7_5
    | ~ spl7_1
    | spl7_29
    | ~ spl7_21
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f378,f309,f229,f388,f70,f97])).

fof(f229,plain,
    ( spl7_21
  <=> ! [X1] :
        ( k1_funct_1(sK2,sK0) = X1
        | ~ r2_hidden(X1,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f309,plain,
    ( spl7_27
  <=> ! [X0] :
        ( k2_enumset1(X0,X0,X0,X0) != k2_relat_1(sK2)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f378,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK2,X1) != X0
        | ~ r2_hidden(X0,k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl7_21
    | ~ spl7_27 ),
    inference(resolution,[],[f369,f58])).

fof(f369,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X7,k2_relat_1(sK2))
        | X6 != X7
        | ~ r2_hidden(X6,k2_relat_1(sK2)) )
    | ~ spl7_21
    | ~ spl7_27 ),
    inference(trivial_inequality_removal,[],[f368])).

fof(f368,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,k2_relat_1(sK2))
        | k2_relat_1(sK2) != k2_relat_1(sK2)
        | X6 != X6
        | X6 != X7
        | ~ r2_hidden(X7,k2_relat_1(sK2)) )
    | ~ spl7_21
    | ~ spl7_27 ),
    inference(duplicate_literal_removal,[],[f366])).

fof(f366,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,k2_relat_1(sK2))
        | ~ r2_hidden(X6,k2_relat_1(sK2))
        | k2_relat_1(sK2) != k2_relat_1(sK2)
        | X6 != X6
        | X6 != X7
        | ~ r2_hidden(X6,k2_relat_1(sK2))
        | ~ r2_hidden(X7,k2_relat_1(sK2)) )
    | ~ spl7_21
    | ~ spl7_27 ),
    inference(superposition,[],[f313,f348])).

fof(f348,plain,
    ( ! [X0,X1] :
        ( sK6(X0,k2_relat_1(sK2)) = X0
        | X0 != X1
        | ~ r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(X1,k2_relat_1(sK2)) )
    | ~ spl7_21
    | ~ spl7_27 ),
    inference(equality_factoring,[],[f326])).

fof(f326,plain,
    ( ! [X6,X5] :
        ( sK6(X5,k2_relat_1(sK2)) = X6
        | sK6(X5,k2_relat_1(sK2)) = X5
        | ~ r2_hidden(X5,k2_relat_1(sK2))
        | ~ r2_hidden(X6,k2_relat_1(sK2)) )
    | ~ spl7_21
    | ~ spl7_27 ),
    inference(trivial_inequality_removal,[],[f324])).

fof(f324,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X5,k2_relat_1(sK2))
        | k2_relat_1(sK2) != k2_relat_1(sK2)
        | sK6(X5,k2_relat_1(sK2)) = X5
        | sK6(X5,k2_relat_1(sK2)) = X6
        | ~ r2_hidden(X6,k2_relat_1(sK2)) )
    | ~ spl7_21
    | ~ spl7_27 ),
    inference(resolution,[],[f312,f232])).

fof(f232,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK2))
        | X0 = X1
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl7_21 ),
    inference(superposition,[],[f230,f230])).

fof(f230,plain,
    ( ! [X1] :
        ( k1_funct_1(sK2,sK0) = X1
        | ~ r2_hidden(X1,k2_relat_1(sK2)) )
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f229])).

fof(f312,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(X0,X1),X1)
        | ~ r2_hidden(X0,k2_relat_1(sK2))
        | k2_relat_1(sK2) != X1
        | sK6(X0,X1) = X0 )
    | ~ spl7_27 ),
    inference(superposition,[],[f310,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | r2_hidden(sK6(X0,X1),X1)
      | sK6(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) = X0
      | r2_hidden(sK6(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f310,plain,
    ( ! [X0] :
        ( k2_enumset1(X0,X0,X0,X0) != k2_relat_1(sK2)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f309])).

fof(f313,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK6(X2,X3),X3)
        | ~ r2_hidden(X2,k2_relat_1(sK2))
        | k2_relat_1(sK2) != X3
        | sK6(X2,X3) != X2 )
    | ~ spl7_27 ),
    inference(superposition,[],[f310,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | ~ r2_hidden(sK6(X0,X1),X1)
      | sK6(X0,X1) != X0 ) ),
    inference(definition_unfolding,[],[f37,f49])).

fof(f37,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X0
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f311,plain,
    ( ~ spl7_17
    | spl7_27
    | spl7_20
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f252,f229,f220,f309,f202])).

fof(f202,plain,
    ( spl7_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f220,plain,
    ( spl7_20
  <=> k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k1_relat_1(sK2),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f252,plain,
    ( ! [X0] :
        ( k2_enumset1(X0,X0,X0,X0) != k2_relat_1(sK2)
        | ~ r2_hidden(X0,k2_relat_1(sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) )
    | spl7_20
    | ~ spl7_21 ),
    inference(superposition,[],[f247,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f247,plain,
    ( ! [X0] :
        ( k2_enumset1(X0,X0,X0,X0) != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | spl7_20
    | ~ spl7_21 ),
    inference(superposition,[],[f222,f230])).

fof(f222,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f220])).

fof(f231,plain,
    ( ~ spl7_5
    | ~ spl7_1
    | spl7_21
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f226,f216,f229,f70,f97])).

fof(f216,plain,
    ( spl7_19
  <=> ! [X0] :
        ( sK0 = sK4(sK2,X0)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f226,plain,
    ( ! [X1] :
        ( k1_funct_1(sK2,sK0) = X1
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X1,k2_relat_1(sK2)) )
    | ~ spl7_19 ),
    inference(duplicate_literal_removal,[],[f225])).

fof(f225,plain,
    ( ! [X1] :
        ( k1_funct_1(sK2,sK0) = X1
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X1,k2_relat_1(sK2))
        | ~ r2_hidden(X1,k2_relat_1(sK2)) )
    | ~ spl7_19 ),
    inference(superposition,[],[f59,f217])).

fof(f217,plain,
    ( ! [X0] :
        ( sK0 = sK4(sK2,X0)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f216])).

fof(f59,plain,(
    ! [X2,X0] :
      ( k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f223,plain,
    ( ~ spl7_20
    | spl7_6
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f175,f170,f102,f220])).

fof(f102,plain,
    ( spl7_6
  <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f170,plain,
    ( spl7_14
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f175,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | spl7_6
    | ~ spl7_14 ),
    inference(backward_demodulation,[],[f104,f172])).

fof(f172,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f104,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f218,plain,
    ( ~ spl7_5
    | ~ spl7_1
    | spl7_19
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f195,f170,f216,f70,f97])).

fof(f195,plain,
    ( ! [X0] :
        ( sK0 = sK4(sK2,X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl7_14 ),
    inference(resolution,[],[f181,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | sK0 = X0 )
    | ~ spl7_14 ),
    inference(superposition,[],[f61,f172])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f35,f49])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f205,plain,
    ( spl7_17
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f176,f170,f87,f202])).

fof(f87,plain,
    ( spl7_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f176,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(backward_demodulation,[],[f89,f172])).

fof(f89,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f188,plain,
    ( spl7_15
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f180,f170,f185])).

fof(f180,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_14 ),
    inference(superposition,[],[f63,f172])).

fof(f63,plain,(
    ! [X2] : r2_hidden(X2,k2_enumset1(X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_enumset1(X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f173,plain,
    ( ~ spl7_4
    | spl7_14
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f163,f157,f170,f87])).

fof(f157,plain,
    ( spl7_13
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f163,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl7_13 ),
    inference(superposition,[],[f159,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f159,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f157])).

fof(f160,plain,
    ( ~ spl7_3
    | spl7_13
    | spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f92,f87,f75,f157,f80])).

fof(f80,plain,
    ( spl7_3
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f75,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f92,plain,
    ( k1_xboole_0 = sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl7_4 ),
    inference(resolution,[],[f89,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f105,plain,(
    ~ spl7_6 ),
    inference(avatar_split_clause,[],[f50,f102])).

fof(f50,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f25,f49,f49])).

fof(f25,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f100,plain,
    ( spl7_5
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f93,f87,f97])).

fof(f93,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_4 ),
    inference(resolution,[],[f89,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f90,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f51,f87])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f23,f49])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f52,f80])).

fof(f52,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f22,f49])).

fof(f22,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f78,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f24,f75])).

fof(f24,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f21,f70])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (13602)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.48  % (13602)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (13594)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f426,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f73,f78,f83,f90,f100,f105,f160,f173,f188,f205,f218,f223,f231,f311,f390,f409,f423])).
% 0.21/0.49  fof(f423,plain,(
% 0.21/0.49    ~spl7_15 | ~spl7_30),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f410])).
% 0.21/0.49  fof(f410,plain,(
% 0.21/0.49    $false | (~spl7_15 | ~spl7_30)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f187,f408])).
% 0.21/0.49  fof(f408,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2))) ) | ~spl7_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f407])).
% 0.21/0.49  fof(f407,plain,(
% 0.21/0.49    spl7_30 <=> ! [X0] : ~r2_hidden(X0,k1_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl7_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f185])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    spl7_15 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.49  fof(f409,plain,(
% 0.21/0.49    ~spl7_5 | ~spl7_1 | spl7_30 | ~spl7_29),
% 0.21/0.49    inference(avatar_split_clause,[],[f405,f388,f407,f70,f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl7_5 <=> v1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl7_1 <=> v1_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.49  fof(f388,plain,(
% 0.21/0.49    spl7_29 <=> ! [X1,X0] : (k1_funct_1(sK2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(sK2)) | ~r2_hidden(X0,k2_relat_1(sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.21/0.49  fof(f405,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_29),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f397])).
% 0.21/0.49  fof(f397,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl7_29),
% 0.21/0.49    inference(resolution,[],[f395,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0,X3] : (r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.49    inference(equality_resolution,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.49  fof(f395,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(sK2))) ) | ~spl7_29),
% 0.21/0.49    inference(equality_resolution,[],[f389])).
% 0.21/0.49  fof(f389,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_funct_1(sK2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(sK2)) | ~r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl7_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f388])).
% 0.21/0.49  fof(f390,plain,(
% 0.21/0.49    ~spl7_5 | ~spl7_1 | spl7_29 | ~spl7_21 | ~spl7_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f378,f309,f229,f388,f70,f97])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    spl7_21 <=> ! [X1] : (k1_funct_1(sK2,sK0) = X1 | ~r2_hidden(X1,k2_relat_1(sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    spl7_27 <=> ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k2_relat_1(sK2) | ~r2_hidden(X0,k2_relat_1(sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.49  fof(f378,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_funct_1(sK2,X1) != X0 | ~r2_hidden(X0,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~r2_hidden(X1,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | (~spl7_21 | ~spl7_27)),
% 0.21/0.49    inference(resolution,[],[f369,f58])).
% 0.21/0.49  fof(f369,plain,(
% 0.21/0.49    ( ! [X6,X7] : (~r2_hidden(X7,k2_relat_1(sK2)) | X6 != X7 | ~r2_hidden(X6,k2_relat_1(sK2))) ) | (~spl7_21 | ~spl7_27)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f368])).
% 0.21/0.49  fof(f368,plain,(
% 0.21/0.49    ( ! [X6,X7] : (~r2_hidden(X6,k2_relat_1(sK2)) | k2_relat_1(sK2) != k2_relat_1(sK2) | X6 != X6 | X6 != X7 | ~r2_hidden(X7,k2_relat_1(sK2))) ) | (~spl7_21 | ~spl7_27)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f366])).
% 0.21/0.49  fof(f366,plain,(
% 0.21/0.49    ( ! [X6,X7] : (~r2_hidden(X6,k2_relat_1(sK2)) | ~r2_hidden(X6,k2_relat_1(sK2)) | k2_relat_1(sK2) != k2_relat_1(sK2) | X6 != X6 | X6 != X7 | ~r2_hidden(X6,k2_relat_1(sK2)) | ~r2_hidden(X7,k2_relat_1(sK2))) ) | (~spl7_21 | ~spl7_27)),
% 0.21/0.49    inference(superposition,[],[f313,f348])).
% 0.21/0.49  fof(f348,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sK6(X0,k2_relat_1(sK2)) = X0 | X0 != X1 | ~r2_hidden(X0,k2_relat_1(sK2)) | ~r2_hidden(X1,k2_relat_1(sK2))) ) | (~spl7_21 | ~spl7_27)),
% 0.21/0.49    inference(equality_factoring,[],[f326])).
% 0.21/0.49  fof(f326,plain,(
% 0.21/0.49    ( ! [X6,X5] : (sK6(X5,k2_relat_1(sK2)) = X6 | sK6(X5,k2_relat_1(sK2)) = X5 | ~r2_hidden(X5,k2_relat_1(sK2)) | ~r2_hidden(X6,k2_relat_1(sK2))) ) | (~spl7_21 | ~spl7_27)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f324])).
% 0.21/0.49  fof(f324,plain,(
% 0.21/0.49    ( ! [X6,X5] : (~r2_hidden(X5,k2_relat_1(sK2)) | k2_relat_1(sK2) != k2_relat_1(sK2) | sK6(X5,k2_relat_1(sK2)) = X5 | sK6(X5,k2_relat_1(sK2)) = X6 | ~r2_hidden(X6,k2_relat_1(sK2))) ) | (~spl7_21 | ~spl7_27)),
% 0.21/0.49    inference(resolution,[],[f312,f232])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k2_relat_1(sK2)) | X0 = X1 | ~r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl7_21),
% 0.21/0.49    inference(superposition,[],[f230,f230])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    ( ! [X1] : (k1_funct_1(sK2,sK0) = X1 | ~r2_hidden(X1,k2_relat_1(sK2))) ) | ~spl7_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f229])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | ~r2_hidden(X0,k2_relat_1(sK2)) | k2_relat_1(sK2) != X1 | sK6(X0,X1) = X0) ) | ~spl7_27),
% 0.21/0.49    inference(superposition,[],[f310,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | r2_hidden(sK6(X0,X1),X1) | sK6(X0,X1) = X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f36,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f26,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f33,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.49  fof(f310,plain,(
% 0.21/0.49    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k2_relat_1(sK2) | ~r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl7_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f309])).
% 0.21/0.49  fof(f313,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~r2_hidden(sK6(X2,X3),X3) | ~r2_hidden(X2,k2_relat_1(sK2)) | k2_relat_1(sK2) != X3 | sK6(X2,X3) != X2) ) | ~spl7_27),
% 0.21/0.49    inference(superposition,[],[f310,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | ~r2_hidden(sK6(X0,X1),X1) | sK6(X0,X1) != X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f37,f49])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f311,plain,(
% 0.21/0.49    ~spl7_17 | spl7_27 | spl7_20 | ~spl7_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f252,f229,f220,f309,f202])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    spl7_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    spl7_20 <=> k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k1_relat_1(sK2),sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k2_relat_1(sK2) | ~r2_hidden(X0,k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))) ) | (spl7_20 | ~spl7_21)),
% 0.21/0.49    inference(superposition,[],[f247,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | ~r2_hidden(X0,k2_relat_1(sK2))) ) | (spl7_20 | ~spl7_21)),
% 0.21/0.49    inference(superposition,[],[f222,f230])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | spl7_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f220])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    ~spl7_5 | ~spl7_1 | spl7_21 | ~spl7_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f226,f216,f229,f70,f97])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    spl7_19 <=> ! [X0] : (sK0 = sK4(sK2,X0) | ~r2_hidden(X0,k2_relat_1(sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    ( ! [X1] : (k1_funct_1(sK2,sK0) = X1 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(X1,k2_relat_1(sK2))) ) | ~spl7_19),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f225])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    ( ! [X1] : (k1_funct_1(sK2,sK0) = X1 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(X1,k2_relat_1(sK2)) | ~r2_hidden(X1,k2_relat_1(sK2))) ) | ~spl7_19),
% 0.21/0.49    inference(superposition,[],[f59,f217])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    ( ! [X0] : (sK0 = sK4(sK2,X0) | ~r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl7_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f216])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X2,X0] : (k1_funct_1(X0,sK4(X0,X2)) = X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK4(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ~spl7_20 | spl7_6 | ~spl7_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f175,f170,f102,f220])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl7_6 <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    spl7_14 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k1_relat_1(sK2),sK1,sK2) | (spl7_6 | ~spl7_14)),
% 0.21/0.49    inference(backward_demodulation,[],[f104,f172])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | ~spl7_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f170])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) | spl7_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f102])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    ~spl7_5 | ~spl7_1 | spl7_19 | ~spl7_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f195,f170,f216,f70,f97])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    ( ! [X0] : (sK0 = sK4(sK2,X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl7_14),
% 0.21/0.49    inference(resolution,[],[f181,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X2,X0] : (r2_hidden(sK4(X0,X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK4(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | sK0 = X0) ) | ~spl7_14),
% 0.21/0.49    inference(superposition,[],[f61,f172])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 0.21/0.49    inference(equality_resolution,[],[f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.49    inference(definition_unfolding,[],[f35,f49])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    spl7_17 | ~spl7_4 | ~spl7_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f176,f170,f87,f202])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl7_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | (~spl7_4 | ~spl7_14)),
% 0.21/0.49    inference(backward_demodulation,[],[f89,f172])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl7_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f87])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    spl7_15 | ~spl7_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f180,f170,f185])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl7_14),
% 0.21/0.49    inference(superposition,[],[f63,f172])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X2] : (r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))) )),
% 0.21/0.49    inference(equality_resolution,[],[f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X2,X1] : (r2_hidden(X2,X1) | k2_enumset1(X2,X2,X2,X2) != X1) )),
% 0.21/0.49    inference(equality_resolution,[],[f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.49    inference(definition_unfolding,[],[f34,f49])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ~spl7_4 | spl7_14 | ~spl7_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f163,f157,f170,f87])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    spl7_13 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl7_13),
% 0.21/0.49    inference(superposition,[],[f159,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~spl7_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f157])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ~spl7_3 | spl7_13 | spl7_2 | ~spl7_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f92,f87,f75,f157,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl7_3 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl7_2 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl7_4),
% 0.21/0.49    inference(resolution,[],[f89,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ~spl7_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f50,f102])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 0.21/0.49    inference(definition_unfolding,[],[f25,f49,f49])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl7_5 | ~spl7_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f93,f87,f97])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    v1_relat_1(sK2) | ~spl7_4),
% 0.21/0.49    inference(resolution,[],[f89,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl7_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f51,f87])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.49    inference(definition_unfolding,[],[f23,f49])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl7_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f80])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.49    inference(definition_unfolding,[],[f22,f49])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ~spl7_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f75])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    k1_xboole_0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl7_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f70])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (13602)------------------------------
% 0.21/0.50  % (13602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13602)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (13602)Memory used [KB]: 11001
% 0.21/0.50  % (13602)Time elapsed: 0.087 s
% 0.21/0.50  % (13602)------------------------------
% 0.21/0.50  % (13602)------------------------------
% 0.21/0.50  % (13573)Success in time 0.144 s
%------------------------------------------------------------------------------

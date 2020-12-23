%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1083+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 147 expanded)
%              Number of leaves         :   25 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  274 ( 656 expanded)
%              Number of equality atoms :   70 ( 137 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f135,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f74,f78,f83,f102,f103,f111,f120,f127,f134])).

fof(f134,plain,
    ( ~ spl3_3
    | spl3_1
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f129,f118,f56,f52,f60])).

fof(f60,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f52,plain,
    ( spl3_1
  <=> k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f56,plain,
    ( spl3_2
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f118,plain,
    ( spl3_14
  <=> ! [X0] :
        ( ~ v5_relat_1(X0,sK0)
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f129,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(resolution,[],[f119,f57])).

fof(f57,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(X0,sK0)
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f118])).

fof(f127,plain,
    ( ~ spl3_4
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl3_4
    | spl3_13 ),
    inference(subsumption_resolution,[],[f65,f125])).

fof(f125,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_13 ),
    inference(resolution,[],[f116,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f116,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_13
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f65,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f120,plain,
    ( ~ spl3_13
    | spl3_14
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f112,f108,f118,f115])).

fof(f108,plain,
    ( spl3_12
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(X0,sK0)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK1)) )
    | ~ spl3_12 ),
    inference(superposition,[],[f91,f109])).

fof(f109,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v5_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f111,plain,
    ( ~ spl3_4
    | spl3_12
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f105,f96,f108,f64])).

fof(f96,plain,
    ( spl3_10
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f105,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_10 ),
    inference(superposition,[],[f39,f97])).

fof(f97,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f103,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != o_0_0_xboole_0
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f102,plain,
    ( spl3_10
    | spl3_11
    | ~ spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f94,f64,f68,f99,f96])).

fof(f99,plain,
    ( spl3_11
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f68,plain,
    ( spl3_5
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f94,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f40,f65])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f20])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f83,plain,
    ( spl3_8
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f79,f76,f81])).

fof(f81,plain,
    ( spl3_8
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f76,plain,
    ( spl3_7
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f79,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl3_7 ),
    inference(resolution,[],[f34,f77])).

fof(f77,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f78,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f33,f76])).

fof(f33,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f74,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f27,f72])).

fof(f72,plain,
    ( spl3_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f27,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v5_relat_1(X2,sK0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X1,sK0,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
            & v5_relat_1(X2,sK0)
            & v1_relat_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X1,sK0,sK0) )
   => ( ? [X2] :
          ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1))
          & v5_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1))
        & v5_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))
      & v5_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0) )
           => ! [X2] :
                ( ( v5_relat_1(X2,X0)
                  & v1_relat_1(X2) )
               => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v5_relat_1(X2,X0)
                  & v1_relat_1(X2) )
               => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
             => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).

fof(f70,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f30,f60])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f31,f56])).

fof(f31,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f32,f52])).

fof(f32,plain,(
    k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f24])).

%------------------------------------------------------------------------------

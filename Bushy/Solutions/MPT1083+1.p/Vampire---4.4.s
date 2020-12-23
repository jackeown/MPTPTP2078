%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t200_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:41 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 166 expanded)
%              Number of leaves         :   24 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :  287 ( 538 expanded)
%              Number of equality atoms :   63 ( 112 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f826,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f103,f109,f113,f117,f131,f135,f140,f175,f187,f229,f269,f400,f440,f792,f812,f825])).

fof(f825,plain,
    ( spl5_146
    | ~ spl5_54
    | ~ spl5_150 ),
    inference(avatar_split_clause,[],[f823,f810,f267,f789])).

fof(f789,plain,
    ( spl5_146
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).

fof(f267,plain,
    ( spl5_54
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f810,plain,
    ( spl5_150
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_150])])).

fof(f823,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl5_54
    | ~ spl5_150 ),
    inference(subsumption_resolution,[],[f814,f268])).

fof(f268,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f267])).

fof(f814,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl5_150 ),
    inference(resolution,[],[f811,f86])).

fof(f86,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t200_funct_2.p',d1_funct_2)).

fof(f811,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_150 ),
    inference(avatar_component_clause,[],[f810])).

fof(f812,plain,
    ( spl5_150
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f462,f438,f810])).

fof(f438,plain,
    ( spl5_82
  <=> r1_tarski(sK1,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f462,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_82 ),
    inference(resolution,[],[f439,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t200_funct_2.p',t3_subset)).

fof(f439,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl5_82 ),
    inference(avatar_component_clause,[],[f438])).

fof(f792,plain,
    ( k1_relat_1(sK1) != k1_relset_1(sK0,sK0,sK1)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | k1_xboole_0 != sK0
    | k1_relat_1(sK1) = sK0 ),
    introduced(theory_axiom,[])).

fof(f440,plain,
    ( spl5_82
    | ~ spl5_16
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f196,f185,f138,f438])).

fof(f138,plain,
    ( spl5_16
  <=> r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f185,plain,
    ( spl5_34
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f196,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl5_16
    | ~ spl5_34 ),
    inference(superposition,[],[f139,f186])).

fof(f186,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f185])).

fof(f139,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f138])).

fof(f400,plain,
    ( ~ spl5_0
    | ~ spl5_8
    | ~ spl5_12
    | spl5_15
    | ~ spl5_48 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_15
    | ~ spl5_48 ),
    inference(subsumption_resolution,[],[f398,f134])).

fof(f134,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_15
  <=> k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f398,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1))
    | ~ spl5_0
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_48 ),
    inference(subsumption_resolution,[],[f397,f93])).

fof(f93,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f397,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1))
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_48 ),
    inference(resolution,[],[f302,f112])).

fof(f112,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_8
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f302,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(X0),sK0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK1)) )
    | ~ spl5_12
    | ~ spl5_48 ),
    inference(subsumption_resolution,[],[f301,f130])).

fof(f130,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_12
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f301,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(X0),sK0)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK1)) )
    | ~ spl5_48 ),
    inference(superposition,[],[f63,f223])).

fof(f223,plain,
    ( k1_relat_1(sK1) = sK0
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl5_48
  <=> k1_relat_1(sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t200_funct_2.p',t46_relat_1)).

fof(f269,plain,
    ( spl5_54
    | ~ spl5_6
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f193,f185,f107,f267])).

fof(f107,plain,
    ( spl5_6
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f193,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_34 ),
    inference(superposition,[],[f108,f186])).

fof(f108,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f229,plain,
    ( spl5_48
    | ~ spl5_28
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f227,f182,f173,f222])).

fof(f173,plain,
    ( spl5_28
  <=> k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f182,plain,
    ( spl5_32
  <=> k1_relset_1(sK0,sK0,sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f227,plain,
    ( k1_relat_1(sK1) = sK0
    | ~ spl5_28
    | ~ spl5_32 ),
    inference(superposition,[],[f183,f174])).

fof(f174,plain,
    ( k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f173])).

fof(f183,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f182])).

fof(f187,plain,
    ( spl5_32
    | spl5_34
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f127,f115,f107,f185,f182])).

fof(f115,plain,
    ( spl5_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f127,plain,
    ( k1_xboole_0 = sK0
    | k1_relset_1(sK0,sK0,sK1) = sK0
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f121,f108])).

fof(f121,plain,
    ( k1_xboole_0 = sK0
    | k1_relset_1(sK0,sK0,sK1) = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ spl5_10 ),
    inference(resolution,[],[f116,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f116,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f175,plain,
    ( spl5_28
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f124,f115,f173])).

fof(f124,plain,
    ( k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)
    | ~ spl5_10 ),
    inference(resolution,[],[f116,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t200_funct_2.p',redefinition_k1_relset_1)).

fof(f140,plain,
    ( spl5_16
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f125,f115,f138])).

fof(f125,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))
    | ~ spl5_10 ),
    inference(resolution,[],[f116,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f135,plain,(
    ~ spl5_15 ),
    inference(avatar_split_clause,[],[f56,f133])).

fof(f56,plain,(
    k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0) )
           => ! [X2] :
                ( ( v5_relat_1(X2,X0)
                  & v1_relat_1(X2) )
               => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t200_funct_2.p',t200_funct_2)).

fof(f131,plain,
    ( spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f123,f115,f129])).

fof(f123,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_10 ),
    inference(resolution,[],[f116,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t200_funct_2.p',cc1_relset_1)).

fof(f117,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f58,f115])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f113,plain,
    ( spl5_8
    | ~ spl5_0
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f105,f101,f92,f111])).

fof(f101,plain,
    ( spl5_4
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f105,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl5_0
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f104,f93])).

fof(f104,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl5_4 ),
    inference(resolution,[],[f102,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t200_funct_2.p',d19_relat_1)).

fof(f102,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f109,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f57,f107])).

fof(f57,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f103,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f55,f101])).

fof(f55,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f54,f92])).

fof(f54,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------

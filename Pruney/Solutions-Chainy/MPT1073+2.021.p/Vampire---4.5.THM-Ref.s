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
% DateTime   : Thu Dec  3 13:07:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 255 expanded)
%              Number of leaves         :   33 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  469 ( 907 expanded)
%              Number of equality atoms :   75 ( 128 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f367,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f80,f84,f88,f92,f106,f117,f120,f126,f139,f188,f195,f221,f228,f244,f339,f358,f362,f366])).

fof(f366,plain,
    ( ~ spl6_41
    | spl6_42 ),
    inference(avatar_split_clause,[],[f365,f356,f352])).

fof(f352,plain,
    ( spl6_41
  <=> r2_hidden(sK5(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f356,plain,
    ( spl6_42
  <=> m1_subset_1(sK5(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f365,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | spl6_42 ),
    inference(resolution,[],[f357,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f357,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),sK1)
    | spl6_42 ),
    inference(avatar_component_clause,[],[f356])).

fof(f362,plain,
    ( ~ spl6_6
    | ~ spl6_2
    | ~ spl6_23
    | spl6_41 ),
    inference(avatar_split_clause,[],[f359,f352,f242,f78,f104])).

fof(f104,plain,
    ( spl6_6
  <=> r2_hidden(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f78,plain,
    ( spl6_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f242,plain,
    ( spl6_23
  <=> k2_relat_1(sK3) = k9_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f359,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl6_2
    | ~ spl6_23
    | spl6_41 ),
    inference(resolution,[],[f353,f246])).

fof(f246,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(X0,sK1,sK3),sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl6_2
    | ~ spl6_23 ),
    inference(superposition,[],[f133,f243])).

fof(f243,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,sK1)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f242])).

fof(f133,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X6))
        | r2_hidden(sK5(X5,X6,sK3),X6) )
    | ~ spl6_2 ),
    inference(resolution,[],[f100,f79])).

fof(f79,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f100,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | r2_hidden(sK5(X0,X2,X1),X2)
      | ~ r2_hidden(X0,k9_relat_1(X1,X2)) ) ),
    inference(resolution,[],[f53,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
            & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
        & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f353,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | spl6_41 ),
    inference(avatar_component_clause,[],[f352])).

fof(f358,plain,
    ( ~ spl6_42
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f346,f337,f356])).

fof(f337,plain,
    ( spl6_38
  <=> sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f346,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),sK1)
    | ~ spl6_38 ),
    inference(trivial_inequality_removal,[],[f345])).

fof(f345,plain,
    ( sK0 != sK0
    | ~ m1_subset_1(sK5(sK0,sK1,sK3),sK1)
    | ~ spl6_38 ),
    inference(superposition,[],[f44,f338])).

fof(f338,plain,
    ( sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f337])).

fof(f44,plain,(
    ! [X4] :
      ( sK0 != k1_funct_1(sK3,X4)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ! [X4] :
        ( sK0 != k1_funct_1(sK3,X4)
        | ~ m1_subset_1(X4,sK1) )
    & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK0 != k1_funct_1(sK3,X4)
          | ~ m1_subset_1(X4,sK1) )
      & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

fof(f339,plain,
    ( spl6_38
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f334,f242,f115,f104,f78,f337])).

fof(f115,plain,
    ( spl6_8
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | k1_funct_1(sK3,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f334,plain,
    ( sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3))
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_23 ),
    inference(resolution,[],[f331,f105])).

fof(f105,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f331,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK5(X0,sK1,sK3)) = X0 )
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_23 ),
    inference(superposition,[],[f329,f243])).

fof(f329,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X3))
        | k1_funct_1(sK3,sK5(X2,X3,sK3)) = X2 )
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(resolution,[],[f327,f116])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | k1_funct_1(sK3,X0) = X1 )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f327,plain,
    ( ! [X6,X5] :
        ( r2_hidden(k4_tarski(sK5(X5,X6,sK3),X5),sK3)
        | ~ r2_hidden(X5,k9_relat_1(sK3,X6)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f121,f79])).

fof(f121,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | r2_hidden(k4_tarski(sK5(X0,X2,X1),X0),X1)
      | ~ r2_hidden(X0,k9_relat_1(X1,X2)) ) ),
    inference(resolution,[],[f52,f55])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f244,plain,
    ( ~ spl6_7
    | spl6_23
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f231,f225,f242,f112])).

fof(f112,plain,
    ( spl6_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f225,plain,
    ( spl6_20
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f231,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl6_20 ),
    inference(superposition,[],[f46,f226])).

fof(f226,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f225])).

fof(f46,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f228,plain,
    ( ~ spl6_2
    | spl6_20
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f223,f182,f225,f78])).

fof(f182,plain,
    ( spl6_13
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f223,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_13 ),
    inference(superposition,[],[f56,f183])).

fof(f183,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f182])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f221,plain,
    ( ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f105,f217])).

fof(f217,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK3))
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f138,f216])).

fof(f216,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f125,f205])).

fof(f205,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(resolution,[],[f194,f96])).

fof(f96,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | ~ r2_hidden(X2,X0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f95,f91])).

fof(f91,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X3,X0) ) ),
    inference(resolution,[],[f49,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f194,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl6_15
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f125,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
        | ~ r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_9
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f138,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(X0,k1_relat_1(sK3),sK3),k1_relat_1(sK3))
        | ~ r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl6_10
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(sK5(X0,k1_relat_1(sK3),sK3),k1_relat_1(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f195,plain,
    ( spl6_15
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f189,f185,f78,f193])).

fof(f185,plain,
    ( spl6_14
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f189,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(superposition,[],[f79,f186])).

fof(f186,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f185])).

fof(f188,plain,
    ( spl6_13
    | spl6_14
    | ~ spl6_3
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f180,f78,f82,f185,f182])).

fof(f82,plain,
    ( spl6_3
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f180,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl6_2 ),
    inference(resolution,[],[f58,f79])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f24])).

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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f139,plain,
    ( ~ spl6_7
    | spl6_10
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f135,f78,f137,f112])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(sK5(X0,k1_relat_1(sK3),sK3),k1_relat_1(sK3))
        | ~ v1_relat_1(sK3) )
    | ~ spl6_2 ),
    inference(superposition,[],[f133,f46])).

fof(f126,plain,
    ( ~ spl6_7
    | spl6_9
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f122,f86,f124,f112])).

% (30627)Refutation not found, incomplete strategy% (30627)------------------------------
% (30627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30627)Termination reason: Refutation not found, incomplete strategy

% (30627)Memory used [KB]: 1663
% (30627)Time elapsed: 0.078 s
% (30627)------------------------------
% (30627)------------------------------
fof(f86,plain,
    ( spl6_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl6_4 ),
    inference(resolution,[],[f72,f87])).

fof(f87,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f72,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f120,plain,
    ( ~ spl6_2
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl6_2
    | spl6_7 ),
    inference(subsumption_resolution,[],[f79,f118])).

fof(f118,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_7 ),
    inference(resolution,[],[f113,f55])).

fof(f113,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f117,plain,
    ( ~ spl6_7
    | spl6_8
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f110,f86,f115,f112])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | k1_funct_1(sK3,X0) = X1
        | ~ v1_relat_1(sK3) )
    | ~ spl6_4 ),
    inference(resolution,[],[f65,f87])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f106,plain,
    ( ~ spl6_2
    | spl6_6
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f101,f74,f104,f78])).

fof(f74,plain,
    ( spl6_1
  <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f101,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_1 ),
    inference(superposition,[],[f75,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f75,plain,
    ( r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f92,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f45,f90])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f88,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f40,f86])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f84,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f41,f82])).

fof(f41,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f42,f78])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f43,f74])).

fof(f43,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:43:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (30616)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (30622)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (30619)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (30620)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (30614)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (30620)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (30623)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (30624)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (30628)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (30627)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f367,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f76,f80,f84,f88,f92,f106,f117,f120,f126,f139,f188,f195,f221,f228,f244,f339,f358,f362,f366])).
% 0.21/0.49  fof(f366,plain,(
% 0.21/0.49    ~spl6_41 | spl6_42),
% 0.21/0.49    inference(avatar_split_clause,[],[f365,f356,f352])).
% 0.21/0.49  fof(f352,plain,(
% 0.21/0.49    spl6_41 <=> r2_hidden(sK5(sK0,sK1,sK3),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.21/0.49  fof(f356,plain,(
% 0.21/0.49    spl6_42 <=> m1_subset_1(sK5(sK0,sK1,sK3),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.21/0.49  fof(f365,plain,(
% 0.21/0.49    ~r2_hidden(sK5(sK0,sK1,sK3),sK1) | spl6_42),
% 0.21/0.49    inference(resolution,[],[f357,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.49  fof(f357,plain,(
% 0.21/0.49    ~m1_subset_1(sK5(sK0,sK1,sK3),sK1) | spl6_42),
% 0.21/0.49    inference(avatar_component_clause,[],[f356])).
% 0.21/0.49  fof(f362,plain,(
% 0.21/0.49    ~spl6_6 | ~spl6_2 | ~spl6_23 | spl6_41),
% 0.21/0.49    inference(avatar_split_clause,[],[f359,f352,f242,f78,f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl6_6 <=> r2_hidden(sK0,k2_relat_1(sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl6_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    spl6_23 <=> k2_relat_1(sK3) = k9_relat_1(sK3,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.49  fof(f359,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k2_relat_1(sK3)) | (~spl6_2 | ~spl6_23 | spl6_41)),
% 0.21/0.49    inference(resolution,[],[f353,f246])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK5(X0,sK1,sK3),sK1) | ~r2_hidden(X0,k2_relat_1(sK3))) ) | (~spl6_2 | ~spl6_23)),
% 0.21/0.49    inference(superposition,[],[f133,f243])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    k2_relat_1(sK3) = k9_relat_1(sK3,sK1) | ~spl6_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f242])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ( ! [X6,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X6)) | r2_hidden(sK5(X5,X6,sK3),X6)) ) | ~spl6_2),
% 0.21/0.49    inference(resolution,[],[f100,f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f78])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | r2_hidden(sK5(X0,X2,X1),X2) | ~r2_hidden(X0,k9_relat_1(X1,X2))) )),
% 0.21/0.49    inference(resolution,[],[f53,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(rectify,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.49  fof(f353,plain,(
% 0.21/0.49    ~r2_hidden(sK5(sK0,sK1,sK3),sK1) | spl6_41),
% 0.21/0.49    inference(avatar_component_clause,[],[f352])).
% 0.21/0.49  fof(f358,plain,(
% 0.21/0.49    ~spl6_42 | ~spl6_38),
% 0.21/0.49    inference(avatar_split_clause,[],[f346,f337,f356])).
% 0.21/0.49  fof(f337,plain,(
% 0.21/0.49    spl6_38 <=> sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.21/0.49  fof(f346,plain,(
% 0.21/0.49    ~m1_subset_1(sK5(sK0,sK1,sK3),sK1) | ~spl6_38),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f345])).
% 0.21/0.49  fof(f345,plain,(
% 0.21/0.49    sK0 != sK0 | ~m1_subset_1(sK5(sK0,sK1,sK3),sK1) | ~spl6_38),
% 0.21/0.49    inference(superposition,[],[f44,f338])).
% 0.21/0.49  fof(f338,plain,(
% 0.21/0.49    sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3)) | ~spl6_38),
% 0.21/0.49    inference(avatar_component_clause,[],[f337])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.49    inference(negated_conjecture,[],[f12])).
% 0.21/0.49  fof(f12,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).
% 0.21/0.49  fof(f339,plain,(
% 0.21/0.49    spl6_38 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f334,f242,f115,f104,f78,f337])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    spl6_8 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.49  fof(f334,plain,(
% 0.21/0.49    sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3)) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_23)),
% 0.21/0.49    inference(resolution,[],[f331,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_relat_1(sK3)) | ~spl6_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f104])).
% 0.21/0.49  fof(f331,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK5(X0,sK1,sK3)) = X0) ) | (~spl6_2 | ~spl6_8 | ~spl6_23)),
% 0.21/0.49    inference(superposition,[],[f329,f243])).
% 0.21/0.49  fof(f329,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~r2_hidden(X2,k9_relat_1(sK3,X3)) | k1_funct_1(sK3,sK5(X2,X3,sK3)) = X2) ) | (~spl6_2 | ~spl6_8)),
% 0.21/0.49    inference(resolution,[],[f327,f116])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1) ) | ~spl6_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f115])).
% 0.21/0.49  fof(f327,plain,(
% 0.21/0.49    ( ! [X6,X5] : (r2_hidden(k4_tarski(sK5(X5,X6,sK3),X5),sK3) | ~r2_hidden(X5,k9_relat_1(sK3,X6))) ) | ~spl6_2),
% 0.21/0.49    inference(resolution,[],[f121,f79])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | r2_hidden(k4_tarski(sK5(X0,X2,X1),X0),X1) | ~r2_hidden(X0,k9_relat_1(X1,X2))) )),
% 0.21/0.49    inference(resolution,[],[f52,f55])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    ~spl6_7 | spl6_23 | ~spl6_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f231,f225,f242,f112])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl6_7 <=> v1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    spl6_20 <=> sK1 = k1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    k2_relat_1(sK3) = k9_relat_1(sK3,sK1) | ~v1_relat_1(sK3) | ~spl6_20),
% 0.21/0.49    inference(superposition,[],[f46,f226])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    sK1 = k1_relat_1(sK3) | ~spl6_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f225])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    ~spl6_2 | spl6_20 | ~spl6_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f223,f182,f225,f78])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    spl6_13 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_13),
% 0.21/0.49    inference(superposition,[],[f56,f183])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl6_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f182])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_15),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f220])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    $false | (~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f105,f217])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3))) ) | (~spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f138,f216])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3))) ) | (~spl6_5 | ~spl6_9 | ~spl6_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f125,f205])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | (~spl6_5 | ~spl6_15)),
% 0.21/0.49    inference(resolution,[],[f194,f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | ~r2_hidden(X2,X0)) ) | ~spl6_5),
% 0.21/0.49    inference(resolution,[],[f95,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0) | ~spl6_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl6_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X3,X0)) )),
% 0.21/0.49    inference(resolution,[],[f49,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(rectify,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~spl6_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f193])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    spl6_15 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~r2_hidden(X0,k1_relat_1(sK3))) ) | ~spl6_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f124])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    spl6_9 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK5(X0,k1_relat_1(sK3),sK3),k1_relat_1(sK3)) | ~r2_hidden(X0,k2_relat_1(sK3))) ) | ~spl6_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f137])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl6_10 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(sK5(X0,k1_relat_1(sK3),sK3),k1_relat_1(sK3)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    spl6_15 | ~spl6_2 | ~spl6_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f189,f185,f78,f193])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    spl6_14 <=> k1_xboole_0 = sK2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl6_2 | ~spl6_14)),
% 0.21/0.49    inference(superposition,[],[f79,f186])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | ~spl6_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f185])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    spl6_13 | spl6_14 | ~spl6_3 | ~spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f180,f78,f82,f185,f182])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl6_3 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl6_2),
% 0.21/0.49    inference(resolution,[],[f58,f79])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    ~spl6_7 | spl6_10 | ~spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f135,f78,f137,f112])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(sK5(X0,k1_relat_1(sK3),sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)) ) | ~spl6_2),
% 0.21/0.49    inference(superposition,[],[f133,f46])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ~spl6_7 | spl6_9 | ~spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f122,f86,f124,f112])).
% 0.21/0.49  % (30627)Refutation not found, incomplete strategy% (30627)------------------------------
% 0.21/0.49  % (30627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30627)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (30627)Memory used [KB]: 1663
% 0.21/0.49  % (30627)Time elapsed: 0.078 s
% 0.21/0.49  % (30627)------------------------------
% 0.21/0.49  % (30627)------------------------------
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl6_4 <=> v1_funct_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~v1_relat_1(sK3)) ) | ~spl6_4),
% 0.21/0.49    inference(resolution,[],[f72,f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    v1_funct_1(sK3) | ~spl6_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f86])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(equality_resolution,[],[f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ~spl6_2 | spl6_7),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f119])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    $false | (~spl6_2 | spl6_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f79,f118])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_7),
% 0.21/0.49    inference(resolution,[],[f113,f55])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | spl6_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f112])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ~spl6_7 | spl6_8 | ~spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f110,f86,f115,f112])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1 | ~v1_relat_1(sK3)) ) | ~spl6_4),
% 0.21/0.49    inference(resolution,[],[f65,f87])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ~spl6_2 | spl6_6 | ~spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f101,f74,f104,f78])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl6_1 <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_1),
% 0.21/0.49    inference(superposition,[],[f75,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) | ~spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f74])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl6_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f90])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f40,f86])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f41,f82])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f78])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f43,f74])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (30620)------------------------------
% 0.21/0.49  % (30620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30620)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (30620)Memory used [KB]: 10874
% 0.21/0.49  % (30620)Time elapsed: 0.073 s
% 0.21/0.49  % (30620)------------------------------
% 0.21/0.49  % (30620)------------------------------
% 0.21/0.50  % (30613)Success in time 0.135 s
%------------------------------------------------------------------------------

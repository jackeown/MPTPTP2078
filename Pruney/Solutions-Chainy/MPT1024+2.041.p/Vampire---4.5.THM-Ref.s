%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 347 expanded)
%              Number of leaves         :   32 ( 136 expanded)
%              Depth                    :   12
%              Number of atoms          :  597 (1101 expanded)
%              Number of equality atoms :   33 (  75 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f352,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f89,f93,f98,f105,f126,f138,f142,f158,f174,f190,f200,f212,f242,f312,f323,f333,f351])).

fof(f351,plain,
    ( ~ spl10_1
    | ~ spl10_3
    | spl10_19
    | ~ spl10_36
    | ~ spl10_37
    | ~ spl10_38 ),
    inference(avatar_contradiction_clause,[],[f350])).

fof(f350,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3
    | spl10_19
    | ~ spl10_36
    | ~ spl10_37
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f349,f88])).

fof(f88,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl10_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f349,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl10_1
    | spl10_19
    | ~ spl10_36
    | ~ spl10_37
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f348,f329])).

fof(f329,plain,
    ( sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | spl10_19
    | ~ spl10_36
    | ~ spl10_37 ),
    inference(subsumption_resolution,[],[f324,f328])).

fof(f328,plain,
    ( r2_hidden(sK6(sK2,sK0,sK3,sK4),sK0)
    | spl10_19
    | ~ spl10_37 ),
    inference(subsumption_resolution,[],[f327,f199])).

fof(f199,plain,
    ( ~ v1_xboole_0(sK0)
    | spl10_19 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl10_19
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f327,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_37 ),
    inference(resolution,[],[f322,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f322,plain,
    ( m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl10_37
  <=> m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f324,plain,
    ( ~ r2_hidden(sK6(sK2,sK0,sK3,sK4),sK0)
    | sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ spl10_36 ),
    inference(resolution,[],[f311,f33])).

fof(f33,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f311,plain,
    ( r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl10_36
  <=> r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f348,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl10_1
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f341,f64])).

fof(f64,plain,
    ( v1_funct_1(sK3)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl10_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f341,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl10_38 ),
    inference(resolution,[],[f332,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f332,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl10_38
  <=> r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f333,plain,
    ( spl10_38
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | ~ spl10_17
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f317,f210,f185,f136,f103,f96,f67,f331])).

fof(f67,plain,
    ( spl10_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f96,plain,
    ( spl10_5
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f103,plain,
    ( spl10_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f136,plain,
    ( spl10_11
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f185,plain,
    ( spl10_17
  <=> r2_hidden(sK8(sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f210,plain,
    ( spl10_22
  <=> m1_subset_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f317,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | ~ spl10_17
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f316,f211])).

fof(f211,plain,
    ( m1_subset_1(sK4,sK1)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f210])).

fof(f316,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f313,f137])).

fof(f137,plain,
    ( ~ v1_xboole_0(sK2)
    | spl10_11 ),
    inference(avatar_component_clause,[],[f136])).

fof(f313,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | ~ spl10_17 ),
    inference(resolution,[],[f194,f97])).

fof(f97,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f194,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X3,sK1)
        | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3) )
    | ~ spl10_2
    | spl10_7
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f181,f191])).

fof(f191,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl10_17 ),
    inference(resolution,[],[f186,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f186,plain,
    ( r2_hidden(sK8(sK0,sK3),sK0)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f185])).

fof(f181,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | v1_xboole_0(X2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X3,sK1)
        | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3) )
    | ~ spl10_2
    | spl10_7 ),
    inference(subsumption_resolution,[],[f180,f104])).

fof(f104,plain,
    ( ~ v1_xboole_0(sK1)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f180,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | v1_xboole_0(X2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X3,sK1)
        | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f176,f68])).

fof(f68,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f176,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | v1_xboole_0(X2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X3,sK1)
        | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(superposition,[],[f45,f71])).

fof(f71,plain,
    ( ! [X3] : k7_relset_1(sK0,sK1,sK3,X3) = k9_relat_1(sK3,X3)
    | ~ spl10_2 ),
    inference(resolution,[],[f68,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(k4_tarski(sK6(X1,X2,X3,X4),X4),X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(f323,plain,
    ( spl10_37
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | ~ spl10_17
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f306,f210,f185,f136,f103,f96,f67,f321])).

fof(f306,plain,
    ( m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | ~ spl10_17
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f305,f211])).

fof(f305,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f302,f137])).

fof(f302,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | ~ spl10_17 ),
    inference(resolution,[],[f195,f97])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,sK1)
        | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0) )
    | ~ spl10_2
    | spl10_7
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f179,f191])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X1,sK1)
        | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0) )
    | ~ spl10_2
    | spl10_7 ),
    inference(subsumption_resolution,[],[f178,f104])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X1,sK1)
        | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f175,f68])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X1,sK1)
        | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(superposition,[],[f44,f71])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | m1_subset_1(sK6(X1,X2,X3,X4),X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f312,plain,
    ( spl10_36
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | ~ spl10_17
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f299,f210,f185,f136,f103,f96,f67,f310])).

fof(f299,plain,
    ( r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | ~ spl10_17
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f298,f211])).

fof(f298,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f295,f137])).

fof(f295,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | ~ spl10_17 ),
    inference(resolution,[],[f193,f97])).

fof(f193,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(X5,sK1)
        | r2_hidden(sK6(X4,sK0,sK3,X5),X4) )
    | ~ spl10_2
    | spl10_7
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f183,f191])).

fof(f183,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | v1_xboole_0(X4)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X5,sK1)
        | r2_hidden(sK6(X4,sK0,sK3,X5),X4) )
    | ~ spl10_2
    | spl10_7 ),
    inference(subsumption_resolution,[],[f182,f104])).

fof(f182,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | v1_xboole_0(X4)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X5,sK1)
        | r2_hidden(sK6(X4,sK0,sK3,X5),X4)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f177,f68])).

fof(f177,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | v1_xboole_0(X4)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X5,sK1)
        | r2_hidden(sK6(X4,sK0,sK3,X5),X4)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(superposition,[],[f46,f71])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(sK6(X1,X2,X3,X4),X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f242,plain,
    ( ~ spl10_1
    | ~ spl10_3
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_15
    | ~ spl10_18 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_15
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f239,f172])).

fof(f172,plain,
    ( ~ r2_hidden(sK7(sK4,sK2,sK3),sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_9
    | ~ spl10_15 ),
    inference(subsumption_resolution,[],[f127,f171])).

fof(f171,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_15 ),
    inference(subsumption_resolution,[],[f170,f88])).

fof(f170,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl10_1
    | ~ spl10_15 ),
    inference(subsumption_resolution,[],[f165,f64])).

fof(f165,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl10_15 ),
    inference(resolution,[],[f157,f38])).

fof(f157,plain,
    ( r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl10_15
  <=> r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f127,plain,
    ( ~ r2_hidden(sK7(sK4,sK2,sK3),sK0)
    | sK4 != k1_funct_1(sK3,sK7(sK4,sK2,sK3))
    | ~ spl10_9 ),
    inference(resolution,[],[f125,f33])).

fof(f125,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl10_9
  <=> r2_hidden(sK7(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f239,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK0)
    | ~ spl10_12
    | ~ spl10_18 ),
    inference(superposition,[],[f141,f189])).

fof(f189,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl10_18
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f141,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl10_12
  <=> r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f212,plain,
    ( spl10_22
    | ~ spl10_2
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f201,f96,f67,f210])).

fof(f201,plain,
    ( m1_subset_1(sK4,sK1)
    | ~ spl10_2
    | ~ spl10_5 ),
    inference(resolution,[],[f112,f81])).

fof(f81,plain,
    ( ! [X4] : m1_subset_1(k9_relat_1(sK3,X4),k1_zfmisc_1(sK1))
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f72,f71])).

fof(f72,plain,
    ( ! [X4] : m1_subset_1(k7_relset_1(sK0,sK1,sK3,X4),k1_zfmisc_1(sK1))
    | ~ spl10_2 ),
    inference(resolution,[],[f68,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f112,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0))
        | m1_subset_1(sK4,X0) )
    | ~ spl10_5 ),
    inference(resolution,[],[f97,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f200,plain,
    ( ~ spl10_19
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f191,f185,f198])).

fof(f190,plain,
    ( spl10_17
    | spl10_18
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f82,f67,f188,f185])).

fof(f82,plain,
    ( sK0 = k1_relat_1(sK3)
    | r2_hidden(sK8(sK0,sK3),sK0)
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f75,f74])).

fof(f74,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl10_2 ),
    inference(resolution,[],[f68,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f75,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | r2_hidden(sK8(sK0,sK3),sK0)
    | ~ spl10_2 ),
    inference(resolution,[],[f68,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK8(X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(f174,plain,
    ( ~ spl10_6
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f166,f156,f100])).

fof(f100,plain,
    ( spl10_6
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f166,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl10_15 ),
    inference(resolution,[],[f157,f43])).

fof(f158,plain,
    ( spl10_15
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f114,f96,f87,f156])).

fof(f114,plain,
    ( r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f109,f88])).

fof(f109,plain,
    ( r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_5 ),
    inference(resolution,[],[f97,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f142,plain,
    ( spl10_12
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f113,f96,f87,f140])).

fof(f113,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f108,f88])).

fof(f108,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl10_5 ),
    inference(resolution,[],[f97,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f138,plain,
    ( ~ spl10_11
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f128,f124,f136])).

fof(f128,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl10_9 ),
    inference(resolution,[],[f125,f43])).

fof(f126,plain,
    ( spl10_9
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f115,f96,f87,f124])).

fof(f115,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f110,f88])).

fof(f110,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl10_5 ),
    inference(resolution,[],[f97,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f105,plain,
    ( spl10_6
    | ~ spl10_7
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f73,f67,f103,f100])).

fof(f73,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | ~ spl10_2 ),
    inference(resolution,[],[f68,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f98,plain,
    ( spl10_5
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f94,f91,f67,f96])).

fof(f91,plain,
    ( spl10_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f94,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f92,f71])).

fof(f92,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f34,f91])).

fof(f34,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,
    ( spl10_3
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f85,f67,f87])).

fof(f85,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f78,f51])).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f78,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | ~ spl10_2 ),
    inference(resolution,[],[f68,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f69,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f36,f67])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f35,f63])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (32109)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.46  % (32111)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (32107)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (32103)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (32103)Refutation not found, incomplete strategy% (32103)------------------------------
% 0.20/0.47  % (32103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (32103)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (32103)Memory used [KB]: 10618
% 0.20/0.47  % (32103)Time elapsed: 0.074 s
% 0.20/0.47  % (32103)------------------------------
% 0.20/0.47  % (32103)------------------------------
% 0.20/0.47  % (32117)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (32119)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.47  % (32108)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (32105)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (32116)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (32104)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (32114)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (32110)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (32106)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (32113)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (32118)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (32122)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (32120)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (32122)Refutation not found, incomplete strategy% (32122)------------------------------
% 0.20/0.50  % (32122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (32122)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (32122)Memory used [KB]: 10618
% 0.20/0.50  % (32122)Time elapsed: 0.100 s
% 0.20/0.50  % (32122)------------------------------
% 0.20/0.50  % (32122)------------------------------
% 0.20/0.50  % (32115)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (32102)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (32112)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (32102)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f352,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f65,f69,f89,f93,f98,f105,f126,f138,f142,f158,f174,f190,f200,f212,f242,f312,f323,f333,f351])).
% 0.20/0.50  fof(f351,plain,(
% 0.20/0.50    ~spl10_1 | ~spl10_3 | spl10_19 | ~spl10_36 | ~spl10_37 | ~spl10_38),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f350])).
% 0.20/0.50  fof(f350,plain,(
% 0.20/0.50    $false | (~spl10_1 | ~spl10_3 | spl10_19 | ~spl10_36 | ~spl10_37 | ~spl10_38)),
% 0.20/0.50    inference(subsumption_resolution,[],[f349,f88])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    v1_relat_1(sK3) | ~spl10_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f87])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    spl10_3 <=> v1_relat_1(sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.50  fof(f349,plain,(
% 0.20/0.50    ~v1_relat_1(sK3) | (~spl10_1 | spl10_19 | ~spl10_36 | ~spl10_37 | ~spl10_38)),
% 0.20/0.50    inference(subsumption_resolution,[],[f348,f329])).
% 0.20/0.50  fof(f329,plain,(
% 0.20/0.50    sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | (spl10_19 | ~spl10_36 | ~spl10_37)),
% 0.20/0.50    inference(subsumption_resolution,[],[f324,f328])).
% 0.20/0.50  fof(f328,plain,(
% 0.20/0.50    r2_hidden(sK6(sK2,sK0,sK3,sK4),sK0) | (spl10_19 | ~spl10_37)),
% 0.20/0.50    inference(subsumption_resolution,[],[f327,f199])).
% 0.20/0.50  fof(f199,plain,(
% 0.20/0.50    ~v1_xboole_0(sK0) | spl10_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f198])).
% 0.20/0.50  fof(f198,plain,(
% 0.20/0.50    spl10_19 <=> v1_xboole_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.20/0.50  fof(f327,plain,(
% 0.20/0.50    v1_xboole_0(sK0) | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK0) | ~spl10_37),
% 0.20/0.50    inference(resolution,[],[f322,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.50  fof(f322,plain,(
% 0.20/0.50    m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | ~spl10_37),
% 0.20/0.50    inference(avatar_component_clause,[],[f321])).
% 0.20/0.50  fof(f321,plain,(
% 0.20/0.50    spl10_37 <=> m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).
% 0.20/0.50  fof(f324,plain,(
% 0.20/0.50    ~r2_hidden(sK6(sK2,sK0,sK3,sK4),sK0) | sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~spl10_36),
% 0.20/0.50    inference(resolution,[],[f311,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f15])).
% 0.20/0.50  fof(f15,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.20/0.50    inference(negated_conjecture,[],[f14])).
% 0.20/0.50  fof(f14,conjecture,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).
% 0.20/0.50  fof(f311,plain,(
% 0.20/0.50    r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | ~spl10_36),
% 0.20/0.50    inference(avatar_component_clause,[],[f310])).
% 0.20/0.50  fof(f310,plain,(
% 0.20/0.50    spl10_36 <=> r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).
% 0.20/0.50  fof(f348,plain,(
% 0.20/0.50    sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3) | (~spl10_1 | ~spl10_38)),
% 0.20/0.50    inference(subsumption_resolution,[],[f341,f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    v1_funct_1(sK3) | ~spl10_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    spl10_1 <=> v1_funct_1(sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.50  fof(f341,plain,(
% 0.20/0.50    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3) | ~spl10_38),
% 0.20/0.50    inference(resolution,[],[f332,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.50  fof(f332,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | ~spl10_38),
% 0.20/0.50    inference(avatar_component_clause,[],[f331])).
% 0.20/0.50  fof(f331,plain,(
% 0.20/0.50    spl10_38 <=> r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).
% 0.20/0.50  fof(f333,plain,(
% 0.20/0.50    spl10_38 | ~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | ~spl10_17 | ~spl10_22),
% 0.20/0.50    inference(avatar_split_clause,[],[f317,f210,f185,f136,f103,f96,f67,f331])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    spl10_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    spl10_5 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    spl10_7 <=> v1_xboole_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    spl10_11 <=> v1_xboole_0(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    spl10_17 <=> r2_hidden(sK8(sK0,sK3),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.20/0.50  fof(f210,plain,(
% 0.20/0.50    spl10_22 <=> m1_subset_1(sK4,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.20/0.50  fof(f317,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | ~spl10_17 | ~spl10_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f316,f211])).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    m1_subset_1(sK4,sK1) | ~spl10_22),
% 0.20/0.50    inference(avatar_component_clause,[],[f210])).
% 0.20/0.50  fof(f316,plain,(
% 0.20/0.50    ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | ~spl10_17)),
% 0.20/0.50    inference(subsumption_resolution,[],[f313,f137])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    ~v1_xboole_0(sK2) | spl10_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f136])).
% 0.20/0.50  fof(f313,plain,(
% 0.20/0.50    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl10_2 | ~spl10_5 | spl10_7 | ~spl10_17)),
% 0.20/0.50    inference(resolution,[],[f194,f97])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl10_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f96])).
% 0.20/0.50  fof(f194,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | ~m1_subset_1(X3,sK1) | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3)) ) | (~spl10_2 | spl10_7 | ~spl10_17)),
% 0.20/0.50    inference(subsumption_resolution,[],[f181,f191])).
% 0.20/0.50  fof(f191,plain,(
% 0.20/0.50    ~v1_xboole_0(sK0) | ~spl10_17),
% 0.20/0.50    inference(resolution,[],[f186,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.50  fof(f186,plain,(
% 0.20/0.50    r2_hidden(sK8(sK0,sK3),sK0) | ~spl10_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f185])).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | v1_xboole_0(sK0) | ~m1_subset_1(X3,sK1) | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3)) ) | (~spl10_2 | spl10_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f180,f104])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    ~v1_xboole_0(sK1) | spl10_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f103])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | v1_xboole_0(sK0) | ~m1_subset_1(X3,sK1) | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f176,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl10_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f67])).
% 0.20/0.50  fof(f176,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X3,sK1) | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.20/0.50    inference(superposition,[],[f45,f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X3] : (k7_relset_1(sK0,sK1,sK3,X3) = k9_relat_1(sK3,X3)) ) | ~spl10_2),
% 0.20/0.50    inference(resolution,[],[f68,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(k4_tarski(sK6(X1,X2,X3,X4),X4),X3) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).
% 0.20/0.50  fof(f323,plain,(
% 0.20/0.50    spl10_37 | ~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | ~spl10_17 | ~spl10_22),
% 0.20/0.50    inference(avatar_split_clause,[],[f306,f210,f185,f136,f103,f96,f67,f321])).
% 0.20/0.50  fof(f306,plain,(
% 0.20/0.50    m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | ~spl10_17 | ~spl10_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f305,f211])).
% 0.20/0.50  fof(f305,plain,(
% 0.20/0.50    ~m1_subset_1(sK4,sK1) | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | ~spl10_17)),
% 0.20/0.50    inference(subsumption_resolution,[],[f302,f137])).
% 0.20/0.50  fof(f302,plain,(
% 0.20/0.50    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl10_2 | ~spl10_5 | spl10_7 | ~spl10_17)),
% 0.20/0.50    inference(resolution,[],[f195,f97])).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | ~m1_subset_1(X1,sK1) | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0)) ) | (~spl10_2 | spl10_7 | ~spl10_17)),
% 0.20/0.50    inference(subsumption_resolution,[],[f179,f191])).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | v1_xboole_0(sK0) | ~m1_subset_1(X1,sK1) | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0)) ) | (~spl10_2 | spl10_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f178,f104])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | v1_xboole_0(sK0) | ~m1_subset_1(X1,sK1) | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f175,f68])).
% 0.20/0.50  fof(f175,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X1,sK1) | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.20/0.50    inference(superposition,[],[f44,f71])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | m1_subset_1(sK6(X1,X2,X3,X4),X2) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f312,plain,(
% 0.20/0.50    spl10_36 | ~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | ~spl10_17 | ~spl10_22),
% 0.20/0.50    inference(avatar_split_clause,[],[f299,f210,f185,f136,f103,f96,f67,f310])).
% 0.20/0.50  fof(f299,plain,(
% 0.20/0.50    r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | ~spl10_17 | ~spl10_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f298,f211])).
% 0.20/0.50  fof(f298,plain,(
% 0.20/0.50    ~m1_subset_1(sK4,sK1) | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | ~spl10_17)),
% 0.20/0.50    inference(subsumption_resolution,[],[f295,f137])).
% 0.20/0.50  fof(f295,plain,(
% 0.20/0.50    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl10_2 | ~spl10_5 | spl10_7 | ~spl10_17)),
% 0.20/0.50    inference(resolution,[],[f193,f97])).
% 0.20/0.50  fof(f193,plain,(
% 0.20/0.50    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | ~m1_subset_1(X5,sK1) | r2_hidden(sK6(X4,sK0,sK3,X5),X4)) ) | (~spl10_2 | spl10_7 | ~spl10_17)),
% 0.20/0.50    inference(subsumption_resolution,[],[f183,f191])).
% 0.20/0.50  fof(f183,plain,(
% 0.20/0.50    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | v1_xboole_0(sK0) | ~m1_subset_1(X5,sK1) | r2_hidden(sK6(X4,sK0,sK3,X5),X4)) ) | (~spl10_2 | spl10_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f182,f104])).
% 0.20/0.50  fof(f182,plain,(
% 0.20/0.50    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | v1_xboole_0(sK0) | ~m1_subset_1(X5,sK1) | r2_hidden(sK6(X4,sK0,sK3,X5),X4) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f177,f68])).
% 0.20/0.50  fof(f177,plain,(
% 0.20/0.50    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X5,sK1) | r2_hidden(sK6(X4,sK0,sK3,X5),X4) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.20/0.50    inference(superposition,[],[f46,f71])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(sK6(X1,X2,X3,X4),X1) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f242,plain,(
% 0.20/0.50    ~spl10_1 | ~spl10_3 | ~spl10_9 | ~spl10_12 | ~spl10_15 | ~spl10_18),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f241])).
% 0.20/0.50  fof(f241,plain,(
% 0.20/0.50    $false | (~spl10_1 | ~spl10_3 | ~spl10_9 | ~spl10_12 | ~spl10_15 | ~spl10_18)),
% 0.20/0.50    inference(subsumption_resolution,[],[f239,f172])).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    ~r2_hidden(sK7(sK4,sK2,sK3),sK0) | (~spl10_1 | ~spl10_3 | ~spl10_9 | ~spl10_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f127,f171])).
% 0.20/0.50  fof(f171,plain,(
% 0.20/0.50    sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3)) | (~spl10_1 | ~spl10_3 | ~spl10_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f170,f88])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3)) | ~v1_relat_1(sK3) | (~spl10_1 | ~spl10_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f165,f64])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3)) | ~v1_relat_1(sK3) | ~spl10_15),
% 0.20/0.50    inference(resolution,[],[f157,f38])).
% 0.20/0.50  fof(f157,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | ~spl10_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f156])).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    spl10_15 <=> r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    ~r2_hidden(sK7(sK4,sK2,sK3),sK0) | sK4 != k1_funct_1(sK3,sK7(sK4,sK2,sK3)) | ~spl10_9),
% 0.20/0.50    inference(resolution,[],[f125,f33])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    r2_hidden(sK7(sK4,sK2,sK3),sK2) | ~spl10_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f124])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    spl10_9 <=> r2_hidden(sK7(sK4,sK2,sK3),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.20/0.50  fof(f239,plain,(
% 0.20/0.50    r2_hidden(sK7(sK4,sK2,sK3),sK0) | (~spl10_12 | ~spl10_18)),
% 0.20/0.50    inference(superposition,[],[f141,f189])).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    sK0 = k1_relat_1(sK3) | ~spl10_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f188])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    spl10_18 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) | ~spl10_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f140])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    spl10_12 <=> r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    spl10_22 | ~spl10_2 | ~spl10_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f201,f96,f67,f210])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    m1_subset_1(sK4,sK1) | (~spl10_2 | ~spl10_5)),
% 0.20/0.50    inference(resolution,[],[f112,f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ( ! [X4] : (m1_subset_1(k9_relat_1(sK3,X4),k1_zfmisc_1(sK1))) ) | ~spl10_2),
% 0.20/0.50    inference(forward_demodulation,[],[f72,f71])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X4] : (m1_subset_1(k7_relset_1(sK0,sK1,sK3,X4),k1_zfmisc_1(sK1))) ) | ~spl10_2),
% 0.20/0.50    inference(resolution,[],[f68,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0)) | m1_subset_1(sK4,X0)) ) | ~spl10_5),
% 0.20/0.50    inference(resolution,[],[f97,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.50  fof(f200,plain,(
% 0.20/0.50    ~spl10_19 | ~spl10_17),
% 0.20/0.50    inference(avatar_split_clause,[],[f191,f185,f198])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    spl10_17 | spl10_18 | ~spl10_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f82,f67,f188,f185])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    sK0 = k1_relat_1(sK3) | r2_hidden(sK8(sK0,sK3),sK0) | ~spl10_2),
% 0.20/0.50    inference(forward_demodulation,[],[f75,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl10_2),
% 0.20/0.50    inference(resolution,[],[f68,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | r2_hidden(sK8(sK0,sK3),sK0) | ~spl10_2),
% 0.20/0.50    inference(resolution,[],[f68,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK8(X1,X2),X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    ~spl10_6 | ~spl10_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f166,f156,f100])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    spl10_6 <=> v1_xboole_0(sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    ~v1_xboole_0(sK3) | ~spl10_15),
% 0.20/0.50    inference(resolution,[],[f157,f43])).
% 0.20/0.50  fof(f158,plain,(
% 0.20/0.50    spl10_15 | ~spl10_3 | ~spl10_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f114,f96,f87,f156])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | (~spl10_3 | ~spl10_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f109,f88])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl10_5),
% 0.20/0.50    inference(resolution,[],[f97,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    spl10_12 | ~spl10_3 | ~spl10_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f113,f96,f87,f140])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) | (~spl10_3 | ~spl10_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f108,f88])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl10_5),
% 0.20/0.50    inference(resolution,[],[f97,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    ~spl10_11 | ~spl10_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f128,f124,f136])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    ~v1_xboole_0(sK2) | ~spl10_9),
% 0.20/0.50    inference(resolution,[],[f125,f43])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    spl10_9 | ~spl10_3 | ~spl10_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f115,f96,f87,f124])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    r2_hidden(sK7(sK4,sK2,sK3),sK2) | (~spl10_3 | ~spl10_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f110,f88])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    r2_hidden(sK7(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | ~spl10_5),
% 0.20/0.50    inference(resolution,[],[f97,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK7(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    spl10_6 | ~spl10_7 | ~spl10_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f73,f67,f103,f100])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ~v1_xboole_0(sK1) | v1_xboole_0(sK3) | ~spl10_2),
% 0.20/0.50    inference(resolution,[],[f68,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    spl10_5 | ~spl10_2 | ~spl10_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f94,f91,f67,f96])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    spl10_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl10_2 | ~spl10_4)),
% 0.20/0.50    inference(forward_demodulation,[],[f92,f71])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl10_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f91])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    spl10_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f34,f91])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    spl10_3 | ~spl10_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f85,f67,f87])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    v1_relat_1(sK3) | ~spl10_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f78,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) | ~spl10_2),
% 0.20/0.50    inference(resolution,[],[f68,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    spl10_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f36,f67])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    spl10_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f35,f63])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    v1_funct_1(sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (32102)------------------------------
% 0.20/0.50  % (32102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (32102)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (32102)Memory used [KB]: 6396
% 0.20/0.50  % (32102)Time elapsed: 0.100 s
% 0.20/0.50  % (32102)------------------------------
% 0.20/0.50  % (32102)------------------------------
% 0.20/0.50  % (32101)Success in time 0.153 s
%------------------------------------------------------------------------------

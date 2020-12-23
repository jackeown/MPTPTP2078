%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 299 expanded)
%              Number of leaves         :   32 ( 120 expanded)
%              Depth                    :   13
%              Number of atoms          :  546 ( 948 expanded)
%              Number of equality atoms :   29 (  60 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f436,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f89,f93,f98,f105,f125,f135,f139,f155,f159,f170,f186,f196,f208,f368,f369,f410,f435])).

fof(f435,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_19
    | ~ spl10_22
    | ~ spl10_38
    | ~ spl10_40 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_19
    | ~ spl10_22
    | ~ spl10_38
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f433,f431])).

fof(f431,plain,
    ( ~ r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_38
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f401,f430])).

fof(f430,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f425,f88])).

fof(f88,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl10_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f425,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl10_1
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f418,f64])).

fof(f64,plain,
    ( v1_funct_1(sK3)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl10_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f418,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl10_40 ),
    inference(resolution,[],[f409,f38])).

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

fof(f409,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f408])).

fof(f408,plain,
    ( spl10_40
  <=> r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f401,plain,
    ( ~ r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4))
    | ~ spl10_38 ),
    inference(resolution,[],[f367,f33])).

fof(f33,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ r2_hidden(X5,sK2)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
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
              | ~ m1_subset_1(X5,X0) )
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
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f367,plain,
    ( m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl10_38
  <=> m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f433,plain,
    ( r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_19
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f432,f207])).

fof(f207,plain,
    ( m1_subset_1(sK4,sK1)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl10_22
  <=> m1_subset_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f432,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_19 ),
    inference(subsumption_resolution,[],[f349,f134])).

fof(f134,plain,
    ( ~ v1_xboole_0(sK2)
    | spl10_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl10_11
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f349,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_19 ),
    inference(resolution,[],[f312,f97])).

fof(f97,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl10_5
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f312,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(X5,sK1)
        | r2_hidden(sK6(X4,sK0,sK3,X5),X4) )
    | ~ spl10_2
    | spl10_7
    | spl10_19 ),
    inference(subsumption_resolution,[],[f179,f195])).

fof(f195,plain,
    ( ~ v1_xboole_0(sK0)
    | spl10_19 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl10_19
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f179,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | v1_xboole_0(X4)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X5,sK1)
        | r2_hidden(sK6(X4,sK0,sK3,X5),X4) )
    | ~ spl10_2
    | spl10_7 ),
    inference(subsumption_resolution,[],[f178,f104])).

fof(f104,plain,
    ( ~ v1_xboole_0(sK1)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl10_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f178,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | v1_xboole_0(X4)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X5,sK1)
        | r2_hidden(sK6(X4,sK0,sK3,X5),X4)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f173,f68])).

fof(f68,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl10_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f173,plain,
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

fof(f410,plain,
    ( spl10_40
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_19
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f392,f206,f194,f133,f103,f96,f67,f408])).

fof(f392,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_19
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f391,f207])).

fof(f391,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_19 ),
    inference(subsumption_resolution,[],[f387,f134])).

fof(f387,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_19 ),
    inference(resolution,[],[f313,f97])).

fof(f313,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X3,sK1)
        | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3) )
    | ~ spl10_2
    | spl10_7
    | spl10_19 ),
    inference(subsumption_resolution,[],[f177,f195])).

fof(f177,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | v1_xboole_0(X2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X3,sK1)
        | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3) )
    | ~ spl10_2
    | spl10_7 ),
    inference(subsumption_resolution,[],[f176,f104])).

fof(f176,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | v1_xboole_0(X2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X3,sK1)
        | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f172,f68])).

fof(f172,plain,
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

fof(f369,plain,
    ( sK0 != k1_relat_1(sK3)
    | v1_xboole_0(k1_relat_1(sK3))
    | ~ v1_xboole_0(sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f368,plain,
    ( spl10_38
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_19
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f362,f206,f194,f133,f103,f96,f67,f366])).

fof(f362,plain,
    ( m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_19
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f361,f207])).

fof(f361,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_11
    | spl10_19 ),
    inference(subsumption_resolution,[],[f358,f134])).

fof(f358,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_2
    | ~ spl10_5
    | spl10_7
    | spl10_19 ),
    inference(resolution,[],[f314,f97])).

fof(f314,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,sK1)
        | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0) )
    | ~ spl10_2
    | spl10_7
    | spl10_19 ),
    inference(subsumption_resolution,[],[f175,f195])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X1,sK1)
        | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0) )
    | ~ spl10_2
    | spl10_7 ),
    inference(subsumption_resolution,[],[f174,f104])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X1,sK1)
        | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f171,f68])).

fof(f171,plain,
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

fof(f208,plain,
    ( spl10_22
    | ~ spl10_2
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f197,f96,f67,f206])).

fof(f197,plain,
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

fof(f196,plain,
    ( ~ spl10_19
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f187,f181,f194])).

fof(f181,plain,
    ( spl10_17
  <=> r2_hidden(sK8(sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f187,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl10_17 ),
    inference(resolution,[],[f182,f43])).

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

fof(f182,plain,
    ( r2_hidden(sK8(sK0,sK3),sK0)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f181])).

fof(f186,plain,
    ( spl10_17
    | spl10_18
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f82,f67,f184,f181])).

fof(f184,plain,
    ( spl10_18
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

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

fof(f170,plain,
    ( ~ spl10_6
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f163,f153,f100])).

fof(f100,plain,
    ( spl10_6
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f153,plain,
    ( spl10_15
  <=> r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f163,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl10_15 ),
    inference(resolution,[],[f154,f43])).

fof(f154,plain,
    ( r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f153])).

fof(f159,plain,
    ( ~ spl10_16
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f148,f137,f157])).

fof(f157,plain,
    ( spl10_16
  <=> v1_xboole_0(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f137,plain,
    ( spl10_12
  <=> r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f148,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK3))
    | ~ spl10_12 ),
    inference(resolution,[],[f138,f43])).

fof(f138,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f155,plain,
    ( spl10_15
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f114,f96,f87,f153])).

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

fof(f139,plain,
    ( spl10_12
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f113,f96,f87,f137])).

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

fof(f135,plain,
    ( ~ spl10_11
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f126,f123,f133])).

fof(f123,plain,
    ( spl10_9
  <=> r2_hidden(sK7(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f126,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl10_9 ),
    inference(resolution,[],[f124,f43])).

fof(f124,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f125,plain,
    ( spl10_9
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f115,f96,f87,f123])).

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

% (26027)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:02:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (26014)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (26022)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (26013)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (26015)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (26021)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (26010)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (26012)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (26024)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (26018)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (26016)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (26011)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (26026)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (26017)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (26023)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (26025)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (26009)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (26028)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (26010)Refutation not found, incomplete strategy% (26010)------------------------------
% 0.21/0.52  % (26010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26010)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (26010)Memory used [KB]: 10618
% 0.21/0.52  % (26010)Time elapsed: 0.073 s
% 0.21/0.52  % (26010)------------------------------
% 0.21/0.52  % (26010)------------------------------
% 0.21/0.52  % (26029)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (26019)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (26029)Refutation not found, incomplete strategy% (26029)------------------------------
% 0.21/0.52  % (26029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26029)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (26029)Memory used [KB]: 10618
% 0.21/0.52  % (26029)Time elapsed: 0.106 s
% 0.21/0.52  % (26029)------------------------------
% 0.21/0.52  % (26029)------------------------------
% 0.21/0.52  % (26020)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (26009)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f436,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f65,f69,f89,f93,f98,f105,f125,f135,f139,f155,f159,f170,f186,f196,f208,f368,f369,f410,f435])).
% 0.21/0.52  fof(f435,plain,(
% 0.21/0.52    ~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_5 | spl10_7 | spl10_11 | spl10_19 | ~spl10_22 | ~spl10_38 | ~spl10_40),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f434])).
% 0.21/0.52  fof(f434,plain,(
% 0.21/0.52    $false | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_5 | spl10_7 | spl10_11 | spl10_19 | ~spl10_22 | ~spl10_38 | ~spl10_40)),
% 0.21/0.52    inference(subsumption_resolution,[],[f433,f431])).
% 0.21/0.52  fof(f431,plain,(
% 0.21/0.52    ~r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl10_1 | ~spl10_3 | ~spl10_38 | ~spl10_40)),
% 0.21/0.52    inference(subsumption_resolution,[],[f401,f430])).
% 0.21/0.52  fof(f430,plain,(
% 0.21/0.52    sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | (~spl10_1 | ~spl10_3 | ~spl10_40)),
% 0.21/0.52    inference(subsumption_resolution,[],[f425,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    v1_relat_1(sK3) | ~spl10_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    spl10_3 <=> v1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.52  fof(f425,plain,(
% 0.21/0.52    sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3) | (~spl10_1 | ~spl10_40)),
% 0.21/0.52    inference(subsumption_resolution,[],[f418,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    v1_funct_1(sK3) | ~spl10_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl10_1 <=> v1_funct_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.52  fof(f418,plain,(
% 0.21/0.52    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3) | ~spl10_40),
% 0.21/0.52    inference(resolution,[],[f409,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.52  fof(f409,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | ~spl10_40),
% 0.21/0.52    inference(avatar_component_clause,[],[f408])).
% 0.21/0.52  fof(f408,plain,(
% 0.21/0.52    spl10_40 <=> r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).
% 0.21/0.52  fof(f401,plain,(
% 0.21/0.52    ~r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | sK4 != k1_funct_1(sK3,sK6(sK2,sK0,sK3,sK4)) | ~spl10_38),
% 0.21/0.52    inference(resolution,[],[f367,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f15])).
% 0.21/0.52  fof(f15,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.52    inference(negated_conjecture,[],[f14])).
% 0.21/0.52  fof(f14,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 0.21/0.52  fof(f367,plain,(
% 0.21/0.52    m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | ~spl10_38),
% 0.21/0.52    inference(avatar_component_clause,[],[f366])).
% 0.21/0.52  fof(f366,plain,(
% 0.21/0.52    spl10_38 <=> m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).
% 0.21/0.52  fof(f433,plain,(
% 0.21/0.52    r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | spl10_19 | ~spl10_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f432,f207])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    m1_subset_1(sK4,sK1) | ~spl10_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f206])).
% 0.21/0.52  fof(f206,plain,(
% 0.21/0.52    spl10_22 <=> m1_subset_1(sK4,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.21/0.52  fof(f432,plain,(
% 0.21/0.52    ~m1_subset_1(sK4,sK1) | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | spl10_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f349,f134])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ~v1_xboole_0(sK2) | spl10_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f133])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    spl10_11 <=> v1_xboole_0(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.52  fof(f349,plain,(
% 0.21/0.52    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(sK6(sK2,sK0,sK3,sK4),sK2) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_19)),
% 0.21/0.52    inference(resolution,[],[f312,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl10_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl10_5 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.52  fof(f312,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | ~m1_subset_1(X5,sK1) | r2_hidden(sK6(X4,sK0,sK3,X5),X4)) ) | (~spl10_2 | spl10_7 | spl10_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f179,f195])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    ~v1_xboole_0(sK0) | spl10_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f194])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    spl10_19 <=> v1_xboole_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | v1_xboole_0(sK0) | ~m1_subset_1(X5,sK1) | r2_hidden(sK6(X4,sK0,sK3,X5),X4)) ) | (~spl10_2 | spl10_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f178,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ~v1_xboole_0(sK1) | spl10_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    spl10_7 <=> v1_xboole_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | v1_xboole_0(sK0) | ~m1_subset_1(X5,sK1) | r2_hidden(sK6(X4,sK0,sK3,X5),X4) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f173,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl10_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    spl10_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X5,sK1) | r2_hidden(sK6(X4,sK0,sK3,X5),X4) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.21/0.52    inference(superposition,[],[f46,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X3] : (k7_relset_1(sK0,sK1,sK3,X3) = k9_relat_1(sK3,X3)) ) | ~spl10_2),
% 0.21/0.52    inference(resolution,[],[f68,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(sK6(X1,X2,X3,X4),X1) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).
% 0.21/0.52  fof(f410,plain,(
% 0.21/0.52    spl10_40 | ~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | spl10_19 | ~spl10_22),
% 0.21/0.52    inference(avatar_split_clause,[],[f392,f206,f194,f133,f103,f96,f67,f408])).
% 0.21/0.52  fof(f392,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | spl10_19 | ~spl10_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f391,f207])).
% 0.21/0.52  fof(f391,plain,(
% 0.21/0.52    ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | spl10_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f387,f134])).
% 0.21/0.52  fof(f387,plain,(
% 0.21/0.52    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK6(sK2,sK0,sK3,sK4),sK4),sK3) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_19)),
% 0.21/0.52    inference(resolution,[],[f313,f97])).
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | ~m1_subset_1(X3,sK1) | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3)) ) | (~spl10_2 | spl10_7 | spl10_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f177,f195])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | v1_xboole_0(sK0) | ~m1_subset_1(X3,sK1) | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3)) ) | (~spl10_2 | spl10_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f176,f104])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | v1_xboole_0(sK0) | ~m1_subset_1(X3,sK1) | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f172,f68])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X3,sK1) | r2_hidden(k4_tarski(sK6(X2,sK0,sK3,X3),X3),sK3) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.21/0.52    inference(superposition,[],[f45,f71])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(k4_tarski(sK6(X1,X2,X3,X4),X4),X3) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f369,plain,(
% 0.21/0.52    sK0 != k1_relat_1(sK3) | v1_xboole_0(k1_relat_1(sK3)) | ~v1_xboole_0(sK0)),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f368,plain,(
% 0.21/0.52    spl10_38 | ~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | spl10_19 | ~spl10_22),
% 0.21/0.52    inference(avatar_split_clause,[],[f362,f206,f194,f133,f103,f96,f67,f366])).
% 0.21/0.52  fof(f362,plain,(
% 0.21/0.52    m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | spl10_19 | ~spl10_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f361,f207])).
% 0.21/0.52  fof(f361,plain,(
% 0.21/0.52    ~m1_subset_1(sK4,sK1) | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_11 | spl10_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f358,f134])).
% 0.21/0.52  fof(f358,plain,(
% 0.21/0.52    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | m1_subset_1(sK6(sK2,sK0,sK3,sK4),sK0) | (~spl10_2 | ~spl10_5 | spl10_7 | spl10_19)),
% 0.21/0.52    inference(resolution,[],[f314,f97])).
% 0.21/0.52  fof(f314,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | ~m1_subset_1(X1,sK1) | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0)) ) | (~spl10_2 | spl10_7 | spl10_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f175,f195])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | v1_xboole_0(sK0) | ~m1_subset_1(X1,sK1) | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0)) ) | (~spl10_2 | spl10_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f174,f104])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | v1_xboole_0(sK0) | ~m1_subset_1(X1,sK1) | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f171,f68])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X1,sK1) | m1_subset_1(sK6(X0,sK0,sK3,X1),sK0) | v1_xboole_0(sK1)) ) | ~spl10_2),
% 0.21/0.52    inference(superposition,[],[f44,f71])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | m1_subset_1(sK6(X1,X2,X3,X4),X2) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    spl10_22 | ~spl10_2 | ~spl10_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f197,f96,f67,f206])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    m1_subset_1(sK4,sK1) | (~spl10_2 | ~spl10_5)),
% 0.21/0.52    inference(resolution,[],[f112,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X4] : (m1_subset_1(k9_relat_1(sK3,X4),k1_zfmisc_1(sK1))) ) | ~spl10_2),
% 0.21/0.52    inference(forward_demodulation,[],[f72,f71])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X4] : (m1_subset_1(k7_relset_1(sK0,sK1,sK3,X4),k1_zfmisc_1(sK1))) ) | ~spl10_2),
% 0.21/0.52    inference(resolution,[],[f68,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0)) | m1_subset_1(sK4,X0)) ) | ~spl10_5),
% 0.21/0.52    inference(resolution,[],[f97,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    ~spl10_19 | ~spl10_17),
% 0.21/0.52    inference(avatar_split_clause,[],[f187,f181,f194])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    spl10_17 <=> r2_hidden(sK8(sK0,sK3),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    ~v1_xboole_0(sK0) | ~spl10_17),
% 0.21/0.52    inference(resolution,[],[f182,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    r2_hidden(sK8(sK0,sK3),sK0) | ~spl10_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f181])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    spl10_17 | spl10_18 | ~spl10_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f82,f67,f184,f181])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    spl10_18 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK3) | r2_hidden(sK8(sK0,sK3),sK0) | ~spl10_2),
% 0.21/0.52    inference(forward_demodulation,[],[f75,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl10_2),
% 0.21/0.52    inference(resolution,[],[f68,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    sK0 = k1_relset_1(sK0,sK1,sK3) | r2_hidden(sK8(sK0,sK3),sK0) | ~spl10_2),
% 0.21/0.52    inference(resolution,[],[f68,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK8(X1,X2),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    ~spl10_6 | ~spl10_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f163,f153,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    spl10_6 <=> v1_xboole_0(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    spl10_15 <=> r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    ~v1_xboole_0(sK3) | ~spl10_15),
% 0.21/0.52    inference(resolution,[],[f154,f43])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | ~spl10_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f153])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    ~spl10_16 | ~spl10_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f148,f137,f157])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    spl10_16 <=> v1_xboole_0(k1_relat_1(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    spl10_12 <=> r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ~v1_xboole_0(k1_relat_1(sK3)) | ~spl10_12),
% 0.21/0.52    inference(resolution,[],[f138,f43])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) | ~spl10_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f137])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    spl10_15 | ~spl10_3 | ~spl10_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f114,f96,f87,f153])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | (~spl10_3 | ~spl10_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f109,f88])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl10_5),
% 0.21/0.52    inference(resolution,[],[f97,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    spl10_12 | ~spl10_3 | ~spl10_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f113,f96,f87,f137])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) | (~spl10_3 | ~spl10_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f108,f88])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl10_5),
% 0.21/0.52    inference(resolution,[],[f97,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    ~spl10_11 | ~spl10_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f126,f123,f133])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    spl10_9 <=> r2_hidden(sK7(sK4,sK2,sK3),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    ~v1_xboole_0(sK2) | ~spl10_9),
% 0.21/0.52    inference(resolution,[],[f124,f43])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    r2_hidden(sK7(sK4,sK2,sK3),sK2) | ~spl10_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f123])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    spl10_9 | ~spl10_3 | ~spl10_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f115,f96,f87,f123])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    r2_hidden(sK7(sK4,sK2,sK3),sK2) | (~spl10_3 | ~spl10_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f110,f88])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    r2_hidden(sK7(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | ~spl10_5),
% 0.21/0.52    inference(resolution,[],[f97,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK7(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl10_6 | ~spl10_7 | ~spl10_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f73,f67,f103,f100])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ~v1_xboole_0(sK1) | v1_xboole_0(sK3) | ~spl10_2),
% 0.21/0.52    inference(resolution,[],[f68,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    spl10_5 | ~spl10_2 | ~spl10_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f94,f91,f67,f96])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    spl10_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.52  % (26027)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl10_2 | ~spl10_4)),
% 0.21/0.52    inference(forward_demodulation,[],[f92,f71])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl10_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f91])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl10_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f34,f91])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    spl10_3 | ~spl10_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f85,f67,f87])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    v1_relat_1(sK3) | ~spl10_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f78,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) | ~spl10_2),
% 0.21/0.52    inference(resolution,[],[f68,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl10_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f36,f67])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    spl10_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f35,f63])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    v1_funct_1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (26009)------------------------------
% 0.21/0.52  % (26009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26009)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (26009)Memory used [KB]: 6396
% 0.21/0.52  % (26009)Time elapsed: 0.086 s
% 0.21/0.52  % (26009)------------------------------
% 0.21/0.52  % (26009)------------------------------
% 0.21/0.52  % (26008)Success in time 0.16 s
%------------------------------------------------------------------------------

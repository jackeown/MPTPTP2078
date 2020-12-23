%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 208 expanded)
%              Number of leaves         :   31 (  86 expanded)
%              Depth                    :    9
%              Number of atoms          :  350 ( 584 expanded)
%              Number of equality atoms :   66 ( 100 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f314,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f81,f85,f89,f106,f117,f122,f126,f135,f141,f148,f168,f182,f265,f274,f282,f283,f293,f313])).

fof(f313,plain,
    ( ~ spl6_1
    | ~ spl6_5
    | ~ spl6_31
    | ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_31
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f311,f105])).

fof(f105,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f311,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl6_1
    | ~ spl6_31
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f310,f287])).

fof(f287,plain,
    ( sK2 != k1_funct_1(sK3,sK5(sK2,sK0,sK3))
    | ~ spl6_31 ),
    inference(resolution,[],[f281,f35])).

fof(f35,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | sK2 != k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

fof(f281,plain,
    ( r2_hidden(sK5(sK2,sK0,sK3),sK0)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl6_31
  <=> r2_hidden(sK5(sK2,sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f310,plain,
    ( sK2 = k1_funct_1(sK3,sK5(sK2,sK0,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_1
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f300,f76])).

fof(f76,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f300,plain,
    ( ~ v1_funct_1(sK3)
    | sK2 = k1_funct_1(sK3,sK5(sK2,sK0,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_32 ),
    inference(resolution,[],[f292,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f292,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK0,sK3),sK2),sK3)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl6_32
  <=> r2_hidden(k4_tarski(sK5(sK2,sK0,sK3),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f293,plain,
    ( spl6_32
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f284,f178,f133,f104,f291])).

fof(f133,plain,
    ( spl6_11
  <=> r2_hidden(sK2,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f178,plain,
    ( spl6_21
  <=> k2_relat_1(sK3) = k9_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f284,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK0,sK3),sK2),sK3)
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_21 ),
    inference(resolution,[],[f221,f134])).

fof(f134,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f221,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK3))
        | r2_hidden(k4_tarski(sK5(X1,sK0,sK3),X1),sK3) )
    | ~ spl6_5
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f217,f105])).

fof(f217,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK3))
        | r2_hidden(k4_tarski(sK5(X1,sK0,sK3),X1),sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl6_21 ),
    inference(superposition,[],[f63,f179])).

fof(f179,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,sK0)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f178])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f283,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3)
    | k2_relat_1(sK3) != k9_relat_1(sK3,k1_relat_1(sK3))
    | k2_relat_1(sK3) = k9_relat_1(sK3,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f282,plain,
    ( spl6_31
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_20
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f278,f178,f175,f133,f104,f280])).

fof(f175,plain,
    ( spl6_20
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f278,plain,
    ( r2_hidden(sK5(sK2,sK0,sK3),sK0)
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_20
    | ~ spl6_21 ),
    inference(resolution,[],[f220,f134])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(sK5(X0,sK0,sK3),sK0) )
    | ~ spl6_5
    | ~ spl6_20
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f219,f176])).

fof(f176,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f175])).

fof(f219,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(sK5(X0,sK0,sK3),k1_relat_1(sK3)) )
    | ~ spl6_5
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f216,f105])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(sK5(X0,sK0,sK3),k1_relat_1(sK3))
        | ~ v1_relat_1(sK3) )
    | ~ spl6_21 ),
    inference(superposition,[],[f62,f179])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f274,plain,(
    ~ spl6_29 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f271,f60])).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f271,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl6_29 ),
    inference(resolution,[],[f264,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f264,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl6_29
  <=> r2_hidden(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f265,plain,
    ( spl6_29
    | ~ spl6_11
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f261,f166,f133,f263])).

fof(f166,plain,
    ( spl6_18
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f261,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl6_11
    | ~ spl6_18 ),
    inference(resolution,[],[f169,f134])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl6_18 ),
    inference(resolution,[],[f167,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f167,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f182,plain,
    ( spl6_20
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f180,f143,f120,f175])).

fof(f120,plain,
    ( spl6_8
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f143,plain,
    ( spl6_13
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f180,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(superposition,[],[f144,f121])).

fof(f121,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f144,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f168,plain,
    ( spl6_18
    | ~ spl6_7
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f158,f146,f115,f166])).

fof(f115,plain,
    ( spl6_7
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f146,plain,
    ( spl6_14
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f158,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_7
    | ~ spl6_14 ),
    inference(superposition,[],[f116,f147])).

fof(f147,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f146])).

fof(f116,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f148,plain,
    ( spl6_13
    | spl6_14
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f97,f83,f79,f146,f143])).

fof(f79,plain,
    ( spl6_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f83,plain,
    ( spl6_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f92,f80])).

fof(f80,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f92,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f84,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f84,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f141,plain,
    ( spl6_12
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f107,f104,f139])).

fof(f139,plain,
    ( spl6_12
  <=> k2_relat_1(sK3) = k9_relat_1(sK3,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f107,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl6_5 ),
    inference(resolution,[],[f105,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f135,plain,
    ( spl6_11
    | ~ spl6_4
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f131,f124,f87,f133])).

fof(f87,plain,
    ( spl6_4
  <=> r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f124,plain,
    ( spl6_9
  <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f131,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | ~ spl6_4
    | ~ spl6_9 ),
    inference(superposition,[],[f88,f125])).

fof(f125,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f88,plain,
    ( r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f126,plain,
    ( spl6_9
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f94,f83,f124])).

fof(f94,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl6_3 ),
    inference(resolution,[],[f84,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f122,plain,
    ( spl6_8
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f90,f83,f120])).

fof(f90,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_3 ),
    inference(resolution,[],[f84,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f117,plain,
    ( spl6_7
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f98,f83,f115])).

fof(f98,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f95,f94])).

fof(f95,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
    | ~ spl6_3 ),
    inference(resolution,[],[f84,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f106,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f93,f83,f104])).

fof(f93,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_3 ),
    inference(resolution,[],[f84,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f89,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f39,f87])).

fof(f39,plain,(
    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f38,f83])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f37,f79])).

fof(f37,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f36,f75])).

fof(f36,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (21539)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.46  % (21521)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (21531)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (21528)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (21525)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (21521)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f314,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f77,f81,f85,f89,f106,f117,f122,f126,f135,f141,f148,f168,f182,f265,f274,f282,f283,f293,f313])).
% 0.20/0.48  fof(f313,plain,(
% 0.20/0.48    ~spl6_1 | ~spl6_5 | ~spl6_31 | ~spl6_32),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f312])).
% 0.20/0.48  fof(f312,plain,(
% 0.20/0.48    $false | (~spl6_1 | ~spl6_5 | ~spl6_31 | ~spl6_32)),
% 0.20/0.48    inference(subsumption_resolution,[],[f311,f105])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    v1_relat_1(sK3) | ~spl6_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f104])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    spl6_5 <=> v1_relat_1(sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.48  fof(f311,plain,(
% 0.20/0.48    ~v1_relat_1(sK3) | (~spl6_1 | ~spl6_31 | ~spl6_32)),
% 0.20/0.48    inference(subsumption_resolution,[],[f310,f287])).
% 0.20/0.48  fof(f287,plain,(
% 0.20/0.48    sK2 != k1_funct_1(sK3,sK5(sK2,sK0,sK3)) | ~spl6_31),
% 0.20/0.48    inference(resolution,[],[f281,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X4] : (~r2_hidden(X4,sK0) | sK2 != k1_funct_1(sK3,X4)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.48    inference(ennf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.20/0.48    inference(negated_conjecture,[],[f15])).
% 0.20/0.48  fof(f15,conjecture,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).
% 0.20/0.48  fof(f281,plain,(
% 0.20/0.48    r2_hidden(sK5(sK2,sK0,sK3),sK0) | ~spl6_31),
% 0.20/0.48    inference(avatar_component_clause,[],[f280])).
% 0.20/0.48  fof(f280,plain,(
% 0.20/0.48    spl6_31 <=> r2_hidden(sK5(sK2,sK0,sK3),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.20/0.48  fof(f310,plain,(
% 0.20/0.48    sK2 = k1_funct_1(sK3,sK5(sK2,sK0,sK3)) | ~v1_relat_1(sK3) | (~spl6_1 | ~spl6_32)),
% 0.20/0.48    inference(subsumption_resolution,[],[f300,f76])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    v1_funct_1(sK3) | ~spl6_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    spl6_1 <=> v1_funct_1(sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.48  fof(f300,plain,(
% 0.20/0.48    ~v1_funct_1(sK3) | sK2 = k1_funct_1(sK3,sK5(sK2,sK0,sK3)) | ~v1_relat_1(sK3) | ~spl6_32),
% 0.20/0.48    inference(resolution,[],[f292,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.48  fof(f292,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK5(sK2,sK0,sK3),sK2),sK3) | ~spl6_32),
% 0.20/0.48    inference(avatar_component_clause,[],[f291])).
% 0.20/0.48  fof(f291,plain,(
% 0.20/0.48    spl6_32 <=> r2_hidden(k4_tarski(sK5(sK2,sK0,sK3),sK2),sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.20/0.48  fof(f293,plain,(
% 0.20/0.48    spl6_32 | ~spl6_5 | ~spl6_11 | ~spl6_21),
% 0.20/0.48    inference(avatar_split_clause,[],[f284,f178,f133,f104,f291])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    spl6_11 <=> r2_hidden(sK2,k2_relat_1(sK3))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.48  fof(f178,plain,(
% 0.20/0.48    spl6_21 <=> k2_relat_1(sK3) = k9_relat_1(sK3,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.48  fof(f284,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK5(sK2,sK0,sK3),sK2),sK3) | (~spl6_5 | ~spl6_11 | ~spl6_21)),
% 0.20/0.48    inference(resolution,[],[f221,f134])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    r2_hidden(sK2,k2_relat_1(sK3)) | ~spl6_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f133])).
% 0.20/0.48  fof(f221,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK3)) | r2_hidden(k4_tarski(sK5(X1,sK0,sK3),X1),sK3)) ) | (~spl6_5 | ~spl6_21)),
% 0.20/0.48    inference(subsumption_resolution,[],[f217,f105])).
% 0.20/0.48  fof(f217,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK3)) | r2_hidden(k4_tarski(sK5(X1,sK0,sK3),X1),sK3) | ~v1_relat_1(sK3)) ) | ~spl6_21),
% 0.20/0.48    inference(superposition,[],[f63,f179])).
% 0.20/0.48  fof(f179,plain,(
% 0.20/0.48    k2_relat_1(sK3) = k9_relat_1(sK3,sK0) | ~spl6_21),
% 0.20/0.48    inference(avatar_component_clause,[],[f178])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.20/0.48  fof(f283,plain,(
% 0.20/0.48    sK0 != k1_relset_1(sK0,sK1,sK3) | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3) | k2_relat_1(sK3) != k9_relat_1(sK3,k1_relat_1(sK3)) | k2_relat_1(sK3) = k9_relat_1(sK3,sK0)),
% 0.20/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.48  fof(f282,plain,(
% 0.20/0.48    spl6_31 | ~spl6_5 | ~spl6_11 | ~spl6_20 | ~spl6_21),
% 0.20/0.48    inference(avatar_split_clause,[],[f278,f178,f175,f133,f104,f280])).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    spl6_20 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.48  fof(f278,plain,(
% 0.20/0.48    r2_hidden(sK5(sK2,sK0,sK3),sK0) | (~spl6_5 | ~spl6_11 | ~spl6_20 | ~spl6_21)),
% 0.20/0.48    inference(resolution,[],[f220,f134])).
% 0.20/0.48  fof(f220,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(sK5(X0,sK0,sK3),sK0)) ) | (~spl6_5 | ~spl6_20 | ~spl6_21)),
% 0.20/0.48    inference(forward_demodulation,[],[f219,f176])).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    sK0 = k1_relat_1(sK3) | ~spl6_20),
% 0.20/0.48    inference(avatar_component_clause,[],[f175])).
% 0.20/0.48  fof(f219,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(sK5(X0,sK0,sK3),k1_relat_1(sK3))) ) | (~spl6_5 | ~spl6_21)),
% 0.20/0.48    inference(subsumption_resolution,[],[f216,f105])).
% 0.20/0.48  fof(f216,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(sK5(X0,sK0,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)) ) | ~spl6_21),
% 0.20/0.48    inference(superposition,[],[f62,f179])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f274,plain,(
% 0.20/0.48    ~spl6_29),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f273])).
% 0.20/0.48  fof(f273,plain,(
% 0.20/0.48    $false | ~spl6_29),
% 0.20/0.48    inference(subsumption_resolution,[],[f271,f60])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.48  fof(f271,plain,(
% 0.20/0.48    ~r1_tarski(k1_xboole_0,sK2) | ~spl6_29),
% 0.20/0.48    inference(resolution,[],[f264,f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.48  fof(f264,plain,(
% 0.20/0.48    r2_hidden(sK2,k1_xboole_0) | ~spl6_29),
% 0.20/0.48    inference(avatar_component_clause,[],[f263])).
% 0.20/0.48  fof(f263,plain,(
% 0.20/0.48    spl6_29 <=> r2_hidden(sK2,k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.20/0.48  fof(f265,plain,(
% 0.20/0.48    spl6_29 | ~spl6_11 | ~spl6_18),
% 0.20/0.48    inference(avatar_split_clause,[],[f261,f166,f133,f263])).
% 0.20/0.48  fof(f166,plain,(
% 0.20/0.48    spl6_18 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.48  fof(f261,plain,(
% 0.20/0.48    r2_hidden(sK2,k1_xboole_0) | (~spl6_11 | ~spl6_18)),
% 0.20/0.48    inference(resolution,[],[f169,f134])).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(X0,k1_xboole_0)) ) | ~spl6_18),
% 0.20/0.48    inference(resolution,[],[f167,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) | ~spl6_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f166])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    spl6_20 | ~spl6_8 | ~spl6_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f180,f143,f120,f175])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    spl6_8 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    spl6_13 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.48  fof(f180,plain,(
% 0.20/0.48    sK0 = k1_relat_1(sK3) | (~spl6_8 | ~spl6_13)),
% 0.20/0.48    inference(superposition,[],[f144,f121])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl6_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f120])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl6_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f143])).
% 0.20/0.48  fof(f168,plain,(
% 0.20/0.48    spl6_18 | ~spl6_7 | ~spl6_14),
% 0.20/0.48    inference(avatar_split_clause,[],[f158,f146,f115,f166])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    spl6_7 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.48  fof(f146,plain,(
% 0.20/0.48    spl6_14 <=> k1_xboole_0 = sK1),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.48  fof(f158,plain,(
% 0.20/0.48    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) | (~spl6_7 | ~spl6_14)),
% 0.20/0.48    inference(superposition,[],[f116,f147])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | ~spl6_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f146])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) | ~spl6_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f115])).
% 0.20/0.48  fof(f148,plain,(
% 0.20/0.48    spl6_13 | spl6_14 | ~spl6_2 | ~spl6_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f97,f83,f79,f146,f143])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    spl6_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    spl6_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl6_2 | ~spl6_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f92,f80])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    v1_funct_2(sK3,sK0,sK1) | ~spl6_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f79])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl6_3),
% 0.20/0.48    inference(resolution,[],[f84,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(flattening,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f83])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    spl6_12 | ~spl6_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f107,f104,f139])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    spl6_12 <=> k2_relat_1(sK3) = k9_relat_1(sK3,k1_relat_1(sK3))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    k2_relat_1(sK3) = k9_relat_1(sK3,k1_relat_1(sK3)) | ~spl6_5),
% 0.20/0.48    inference(resolution,[],[f105,f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    spl6_11 | ~spl6_4 | ~spl6_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f131,f124,f87,f133])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    spl6_4 <=> r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    spl6_9 <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    r2_hidden(sK2,k2_relat_1(sK3)) | (~spl6_4 | ~spl6_9)),
% 0.20/0.48    inference(superposition,[],[f88,f125])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl6_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f124])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) | ~spl6_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f87])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    spl6_9 | ~spl6_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f94,f83,f124])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl6_3),
% 0.20/0.48    inference(resolution,[],[f84,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    spl6_8 | ~spl6_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f90,f83,f120])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl6_3),
% 0.20/0.48    inference(resolution,[],[f84,f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    spl6_7 | ~spl6_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f98,f83,f115])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) | ~spl6_3),
% 0.20/0.48    inference(forward_demodulation,[],[f95,f94])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) | ~spl6_3),
% 0.20/0.48    inference(resolution,[],[f84,f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    spl6_5 | ~spl6_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f93,f83,f104])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    v1_relat_1(sK3) | ~spl6_3),
% 0.20/0.48    inference(resolution,[],[f84,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    spl6_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f39,f87])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    spl6_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f38,f83])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    spl6_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f37,f79])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    spl6_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f36,f75])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    v1_funct_1(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (21521)------------------------------
% 0.20/0.48  % (21521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (21521)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (21521)Memory used [KB]: 6268
% 0.20/0.48  % (21521)Time elapsed: 0.066 s
% 0.20/0.48  % (21521)------------------------------
% 0.20/0.48  % (21521)------------------------------
% 0.20/0.48  % (21533)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (21520)Success in time 0.129 s
%------------------------------------------------------------------------------

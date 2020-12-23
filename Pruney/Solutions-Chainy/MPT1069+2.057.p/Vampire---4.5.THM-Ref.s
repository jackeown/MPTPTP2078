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
% DateTime   : Thu Dec  3 13:07:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 439 expanded)
%              Number of leaves         :   56 ( 213 expanded)
%              Depth                    :   11
%              Number of atoms          :  770 (2069 expanded)
%              Number of equality atoms :  111 ( 413 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f597,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f90,f94,f98,f102,f106,f110,f114,f118,f122,f153,f159,f163,f169,f173,f184,f219,f223,f227,f257,f263,f266,f310,f326,f328,f335,f364,f389,f396,f403,f408,f425,f519,f583,f588,f594,f596])).

fof(f596,plain,(
    spl6_78 ),
    inference(avatar_contradiction_clause,[],[f595])).

fof(f595,plain,
    ( $false
    | spl6_78 ),
    inference(resolution,[],[f593,f57])).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f593,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5))
    | spl6_78 ),
    inference(avatar_component_clause,[],[f592])).

fof(f592,plain,
    ( spl6_78
  <=> r1_tarski(k1_xboole_0,k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f594,plain,
    ( ~ spl6_78
    | spl6_30
    | ~ spl6_77 ),
    inference(avatar_split_clause,[],[f589,f586,f225,f592])).

fof(f225,plain,
    ( spl6_30
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f586,plain,
    ( spl6_77
  <=> m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f589,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5))
    | spl6_30
    | ~ spl6_77 ),
    inference(resolution,[],[f587,f267])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | ~ r1_tarski(k1_xboole_0,X0) )
    | spl6_30 ),
    inference(resolution,[],[f226,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f63,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f226,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_30 ),
    inference(avatar_component_clause,[],[f225])).

fof(f587,plain,
    ( m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5),k1_xboole_0)
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f586])).

fof(f588,plain,
    ( spl6_77
    | ~ spl6_4
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f584,f581,f96,f586])).

fof(f96,plain,
    ( spl6_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f581,plain,
    ( spl6_76
  <=> ! [X0] :
        ( m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0),k1_xboole_0)
        | ~ m1_subset_1(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f584,plain,
    ( m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5),k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_76 ),
    inference(resolution,[],[f582,f97])).

fof(f97,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f582,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0),k1_xboole_0) )
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f581])).

fof(f583,plain,
    ( spl6_44
    | ~ spl6_65
    | spl6_76
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_21
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f578,f307,f179,f116,f108,f581,f496,f321])).

fof(f321,plain,
    ( spl6_44
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

% (3279)Refutation not found, incomplete strategy% (3279)------------------------------
% (3279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f496,plain,
    ( spl6_65
  <=> v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

% (3279)Termination reason: Refutation not found, incomplete strategy

fof(f108,plain,
    ( spl6_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

% (3279)Memory used [KB]: 10618
% (3279)Time elapsed: 0.095 s
fof(f116,plain,
    ( spl6_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

% (3279)------------------------------
% (3279)------------------------------
fof(f179,plain,
    ( spl6_21
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f307,plain,
    ( spl6_42
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f578,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0),k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK1) )
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_21
    | ~ spl6_42 ),
    inference(forward_demodulation,[],[f577,f308])).

fof(f308,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f307])).

fof(f577,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_funct_2(sK1,k1_xboole_0,sK3,X0),k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK1) )
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_21
    | ~ spl6_42 ),
    inference(forward_demodulation,[],[f576,f180])).

fof(f180,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f179])).

fof(f576,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
        | ~ m1_subset_1(X0,sK1)
        | m1_subset_1(k3_funct_2(sK1,sK2,sK3,X0),sK2)
        | v1_xboole_0(sK1) )
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_21
    | ~ spl6_42 ),
    inference(forward_demodulation,[],[f575,f308])).

fof(f575,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,k1_xboole_0)
        | ~ m1_subset_1(X0,sK1)
        | m1_subset_1(k3_funct_2(sK1,sK2,sK3,X0),sK2)
        | v1_xboole_0(sK1) )
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f573,f180])).

fof(f573,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ v1_funct_2(sK3,sK1,sK2)
        | m1_subset_1(k3_funct_2(sK1,sK2,sK3,X0),sK2)
        | v1_xboole_0(sK1) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(resolution,[],[f316,f109])).

fof(f109,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f316,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ m1_subset_1(X3,X4)
        | ~ v1_funct_2(sK3,X4,X5)
        | m1_subset_1(k3_funct_2(X4,X5,sK3,X3),X5)
        | v1_xboole_0(X4) )
    | ~ spl6_9 ),
    inference(resolution,[],[f77,f117])).

fof(f117,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f519,plain,
    ( spl6_65
    | ~ spl6_29
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f470,f307,f221,f496])).

fof(f221,plain,
    ( spl6_29
  <=> v1_funct_2(sK3,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f470,plain,
    ( v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
    | ~ spl6_29
    | ~ spl6_42 ),
    inference(superposition,[],[f222,f308])).

fof(f222,plain,
    ( v1_funct_2(sK3,sK1,k1_xboole_0)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f221])).

fof(f425,plain,
    ( ~ spl6_19
    | ~ spl6_46
    | spl6_55 ),
    inference(avatar_split_clause,[],[f422,f387,f333,f167])).

fof(f167,plain,
    ( spl6_19
  <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f333,plain,
    ( spl6_46
  <=> ! [X2] :
        ( r2_hidden(k1_funct_1(sK3,sK5),X2)
        | ~ r1_tarski(k2_relat_1(sK3),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f387,plain,
    ( spl6_55
  <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f422,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl6_46
    | spl6_55 ),
    inference(resolution,[],[f388,f334])).

fof(f334,plain,
    ( ! [X2] :
        ( r2_hidden(k1_funct_1(sK3,sK5),X2)
        | ~ r1_tarski(k2_relat_1(sK3),X2) )
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f333])).

fof(f388,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | spl6_55 ),
    inference(avatar_component_clause,[],[f387])).

fof(f408,plain,
    ( ~ spl6_5
    | spl6_54 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | ~ spl6_5
    | spl6_54 ),
    inference(subsumption_resolution,[],[f101,f404])).

fof(f404,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl6_54 ),
    inference(resolution,[],[f385,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f385,plain,
    ( ~ v5_relat_1(sK4,sK0)
    | spl6_54 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl6_54
  <=> v5_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f101,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f403,plain,(
    spl6_56 ),
    inference(avatar_contradiction_clause,[],[f401])).

fof(f401,plain,
    ( $false
    | spl6_56 ),
    inference(resolution,[],[f395,f60])).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f395,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | spl6_56 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl6_56
  <=> v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f396,plain,
    ( ~ spl6_56
    | ~ spl6_5
    | spl6_53 ),
    inference(avatar_split_clause,[],[f391,f381,f100,f394])).

fof(f381,plain,
    ( spl6_53
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f391,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | ~ spl6_5
    | spl6_53 ),
    inference(resolution,[],[f390,f101])).

fof(f390,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_53 ),
    inference(resolution,[],[f382,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f382,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_53 ),
    inference(avatar_component_clause,[],[f381])).

fof(f389,plain,
    ( ~ spl6_53
    | ~ spl6_54
    | ~ spl6_6
    | ~ spl6_55
    | spl6_50 ),
    inference(avatar_split_clause,[],[f379,f361,f387,f104,f384,f381])).

fof(f104,plain,
    ( spl6_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f361,plain,
    ( spl6_50
  <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f379,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | spl6_50 ),
    inference(trivial_inequality_removal,[],[f378])).

fof(f378,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | spl6_50 ),
    inference(superposition,[],[f362,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f362,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_50 ),
    inference(avatar_component_clause,[],[f361])).

fof(f364,plain,
    ( spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | spl6_2
    | ~ spl6_50
    | ~ spl6_20
    | spl6_1
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f354,f157,f84,f171,f361,f88,f96,f100,f104,f108,f112,f116,f120])).

fof(f120,plain,
    ( spl6_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f112,plain,
    ( spl6_8
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f88,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f171,plain,
    ( spl6_20
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f84,plain,
    ( spl6_1
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f157,plain,
    ( spl6_17
  <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f354,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | spl6_1
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f353,f158])).

fof(f158,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f157])).

fof(f353,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | spl6_1 ),
    inference(superposition,[],[f85,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f85,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f335,plain,
    ( ~ spl6_36
    | spl6_46
    | ~ spl6_4
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f331,f324,f96,f333,f251])).

fof(f251,plain,
    ( spl6_36
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f324,plain,
    ( spl6_45
  <=> ! [X1,X0] :
        ( ~ v5_relat_1(sK3,X0)
        | ~ m1_subset_1(X1,sK1)
        | r2_hidden(k1_funct_1(sK3,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

% (3267)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f331,plain,
    ( ! [X2] :
        ( r2_hidden(k1_funct_1(sK3,sK5),X2)
        | ~ r1_tarski(k2_relat_1(sK3),X2)
        | ~ v1_relat_1(sK3) )
    | ~ spl6_4
    | ~ spl6_45 ),
    inference(resolution,[],[f329,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f329,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK3,X0)
        | r2_hidden(k1_funct_1(sK3,sK5),X0) )
    | ~ spl6_4
    | ~ spl6_45 ),
    inference(resolution,[],[f325,f97])).

fof(f325,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,sK1)
        | ~ v5_relat_1(sK3,X0)
        | r2_hidden(k1_funct_1(sK3,X1),X0) )
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f324])).

fof(f328,plain,
    ( spl6_2
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f327,f321,f88])).

fof(f327,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_44 ),
    inference(resolution,[],[f322,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f322,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f321])).

fof(f326,plain,
    ( spl6_44
    | spl6_45
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f319,f255,f324,f321])).

fof(f255,plain,
    ( spl6_37
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v5_relat_1(sK3,X1)
        | r2_hidden(k1_funct_1(sK3,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f319,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(sK3,X0)
        | r2_hidden(k1_funct_1(sK3,X1),X0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X1,sK1) )
    | ~ spl6_37 ),
    inference(resolution,[],[f256,f63])).

fof(f256,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v5_relat_1(sK3,X1)
        | r2_hidden(k1_funct_1(sK3,X0),X1) )
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f255])).

fof(f310,plain,
    ( spl6_42
    | spl6_2
    | ~ spl6_29
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f303,f217,f221,f88,f307])).

fof(f217,plain,
    ( spl6_28
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f303,plain,
    ( ~ v1_funct_2(sK3,sK1,k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3
    | ~ spl6_28 ),
    inference(resolution,[],[f218,f80])).

fof(f80,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f218,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f217])).

fof(f266,plain,(
    spl6_38 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | spl6_38 ),
    inference(resolution,[],[f262,f60])).

fof(f262,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | spl6_38 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl6_38
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f263,plain,
    ( ~ spl6_38
    | ~ spl6_7
    | spl6_36 ),
    inference(avatar_split_clause,[],[f259,f251,f108,f261])).

fof(f259,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | ~ spl6_7
    | spl6_36 ),
    inference(resolution,[],[f258,f109])).

fof(f258,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_36 ),
    inference(resolution,[],[f252,f58])).

fof(f252,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_36 ),
    inference(avatar_component_clause,[],[f251])).

fof(f257,plain,
    ( ~ spl6_36
    | ~ spl6_9
    | spl6_37
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f249,f182,f255,f116,f251])).

fof(f182,plain,
    ( spl6_22
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),X1)
        | ~ v1_funct_1(sK3)
        | ~ v5_relat_1(sK3,X1)
        | ~ v1_relat_1(sK3) )
    | ~ spl6_22 ),
    inference(superposition,[],[f64,f183])).

fof(f183,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f182])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f227,plain,
    ( ~ spl6_30
    | spl6_10
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f196,f179,f120,f225])).

fof(f196,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_10
    | ~ spl6_21 ),
    inference(superposition,[],[f121,f180])).

fof(f121,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f223,plain,
    ( spl6_29
    | ~ spl6_8
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f195,f179,f112,f221])).

fof(f195,plain,
    ( v1_funct_2(sK3,sK1,k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_21 ),
    inference(superposition,[],[f113,f180])).

fof(f113,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f219,plain,
    ( spl6_28
    | ~ spl6_7
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f194,f179,f108,f217])).

fof(f194,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_7
    | ~ spl6_21 ),
    inference(superposition,[],[f109,f180])).

fof(f184,plain,
    ( ~ spl6_7
    | spl6_21
    | spl6_22
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f177,f161,f112,f182,f179,f108])).

fof(f161,plain,
    ( spl6_18
  <=> k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f177,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f176,f162])).

fof(f162,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f176,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_8 ),
    inference(resolution,[],[f71,f113])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f173,plain,
    ( spl6_20
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f165,f157,f92,f171])).

fof(f92,plain,
    ( spl6_3
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f165,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(superposition,[],[f93,f158])).

fof(f93,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f169,plain,
    ( spl6_19
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f164,f157,f151,f167])).

fof(f151,plain,
    ( spl6_16
  <=> r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f164,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(superposition,[],[f152,f158])).

fof(f152,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f151])).

fof(f163,plain,
    ( spl6_18
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f155,f108,f161])).

fof(f155,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)
    | ~ spl6_7 ),
    inference(resolution,[],[f69,f109])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f159,plain,
    ( spl6_17
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f154,f100,f157])).

fof(f154,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl6_5 ),
    inference(resolution,[],[f69,f101])).

fof(f153,plain,
    ( ~ spl6_7
    | spl6_16
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f148,f92,f151,f108])).

fof(f148,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_3 ),
    inference(superposition,[],[f93,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f122,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f47,f120])).

fof(f47,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f43,f42,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK1
                  & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK1
                & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
              & k1_xboole_0 != sK1
              & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
            & k1_xboole_0 != sK1
            & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
          & k1_xboole_0 != sK1
          & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
        & k1_xboole_0 != sK1
        & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
        & m1_subset_1(X5,sK1) )
   => ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
      & k1_xboole_0 != sK1
      & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(f118,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f48,f116])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f114,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f49,f112])).

fof(f49,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f110,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f50,f108])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f106,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f51,f104])).

fof(f51,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f102,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f52,f100])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f98,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f53,f96])).

fof(f53,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f94,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f54,f92])).

fof(f54,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f55,f88])).

fof(f55,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f86,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f56,f84])).

fof(f56,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:12:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (3264)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (3273)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (3279)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (3270)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (3265)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (3260)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (3271)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (3259)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (3260)Refutation not found, incomplete strategy% (3260)------------------------------
% 0.21/0.49  % (3260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3260)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (3260)Memory used [KB]: 10618
% 0.21/0.49  % (3260)Time elapsed: 0.072 s
% 0.21/0.49  % (3260)------------------------------
% 0.21/0.49  % (3260)------------------------------
% 0.21/0.49  % (3270)Refutation not found, incomplete strategy% (3270)------------------------------
% 0.21/0.49  % (3270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3270)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (3270)Memory used [KB]: 10746
% 0.21/0.49  % (3270)Time elapsed: 0.079 s
% 0.21/0.49  % (3270)------------------------------
% 0.21/0.49  % (3270)------------------------------
% 0.21/0.50  % (3271)Refutation not found, incomplete strategy% (3271)------------------------------
% 0.21/0.50  % (3271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3271)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (3271)Memory used [KB]: 6396
% 0.21/0.50  % (3271)Time elapsed: 0.074 s
% 0.21/0.50  % (3271)------------------------------
% 0.21/0.50  % (3271)------------------------------
% 0.21/0.50  % (3274)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (3262)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (3278)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (3272)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (3276)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (3266)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (3263)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (3261)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (3277)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (3265)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f597,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f86,f90,f94,f98,f102,f106,f110,f114,f118,f122,f153,f159,f163,f169,f173,f184,f219,f223,f227,f257,f263,f266,f310,f326,f328,f335,f364,f389,f396,f403,f408,f425,f519,f583,f588,f594,f596])).
% 0.21/0.51  fof(f596,plain,(
% 0.21/0.51    spl6_78),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f595])).
% 0.21/0.51  fof(f595,plain,(
% 0.21/0.51    $false | spl6_78),
% 0.21/0.51    inference(resolution,[],[f593,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.51  fof(f593,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5)) | spl6_78),
% 0.21/0.51    inference(avatar_component_clause,[],[f592])).
% 0.21/0.51  fof(f592,plain,(
% 0.21/0.51    spl6_78 <=> r1_tarski(k1_xboole_0,k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 0.21/0.51  fof(f594,plain,(
% 0.21/0.51    ~spl6_78 | spl6_30 | ~spl6_77),
% 0.21/0.51    inference(avatar_split_clause,[],[f589,f586,f225,f592])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    spl6_30 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.51  fof(f586,plain,(
% 0.21/0.51    spl6_77 <=> m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).
% 0.21/0.51  fof(f589,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5)) | (spl6_30 | ~spl6_77)),
% 0.21/0.51    inference(resolution,[],[f587,f267])).
% 0.21/0.51  fof(f267,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X0)) ) | spl6_30),
% 0.21/0.51    inference(resolution,[],[f226,f123])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f63,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    ~v1_xboole_0(k1_xboole_0) | spl6_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f225])).
% 0.21/0.51  fof(f587,plain,(
% 0.21/0.51    m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5),k1_xboole_0) | ~spl6_77),
% 0.21/0.51    inference(avatar_component_clause,[],[f586])).
% 0.21/0.51  fof(f588,plain,(
% 0.21/0.51    spl6_77 | ~spl6_4 | ~spl6_76),
% 0.21/0.51    inference(avatar_split_clause,[],[f584,f581,f96,f586])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl6_4 <=> m1_subset_1(sK5,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.51  fof(f581,plain,(
% 0.21/0.51    spl6_76 <=> ! [X0] : (m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0),k1_xboole_0) | ~m1_subset_1(X0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).
% 0.21/0.51  fof(f584,plain,(
% 0.21/0.51    m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5),k1_xboole_0) | (~spl6_4 | ~spl6_76)),
% 0.21/0.51    inference(resolution,[],[f582,f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    m1_subset_1(sK5,sK1) | ~spl6_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f582,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0),k1_xboole_0)) ) | ~spl6_76),
% 0.21/0.51    inference(avatar_component_clause,[],[f581])).
% 0.21/0.51  fof(f583,plain,(
% 0.21/0.51    spl6_44 | ~spl6_65 | spl6_76 | ~spl6_7 | ~spl6_9 | ~spl6_21 | ~spl6_42),
% 0.21/0.51    inference(avatar_split_clause,[],[f578,f307,f179,f116,f108,f581,f496,f321])).
% 0.21/0.51  fof(f321,plain,(
% 0.21/0.51    spl6_44 <=> v1_xboole_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.21/0.51  % (3279)Refutation not found, incomplete strategy% (3279)------------------------------
% 0.21/0.51  % (3279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  fof(f496,plain,(
% 0.21/0.51    spl6_65 <=> v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 0.21/0.51  % (3279)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    spl6_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.51  % (3279)Memory used [KB]: 10618
% 0.21/0.51  % (3279)Time elapsed: 0.095 s
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl6_9 <=> v1_funct_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.51  % (3279)------------------------------
% 0.21/0.51  % (3279)------------------------------
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    spl6_21 <=> k1_xboole_0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.51  fof(f307,plain,(
% 0.21/0.51    spl6_42 <=> k1_xboole_0 = sK3),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.21/0.51  fof(f578,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK1)) ) | (~spl6_7 | ~spl6_9 | ~spl6_21 | ~spl6_42)),
% 0.21/0.51    inference(forward_demodulation,[],[f577,f308])).
% 0.21/0.51  fof(f308,plain,(
% 0.21/0.51    k1_xboole_0 = sK3 | ~spl6_42),
% 0.21/0.51    inference(avatar_component_clause,[],[f307])).
% 0.21/0.51  fof(f577,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k3_funct_2(sK1,k1_xboole_0,sK3,X0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK1)) ) | (~spl6_7 | ~spl6_9 | ~spl6_21 | ~spl6_42)),
% 0.21/0.51    inference(forward_demodulation,[],[f576,f180])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~spl6_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f179])).
% 0.21/0.51  fof(f576,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | ~m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,sK2,sK3,X0),sK2) | v1_xboole_0(sK1)) ) | (~spl6_7 | ~spl6_9 | ~spl6_21 | ~spl6_42)),
% 0.21/0.51    inference(forward_demodulation,[],[f575,f308])).
% 0.21/0.51  fof(f575,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_2(sK3,sK1,k1_xboole_0) | ~m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,sK2,sK3,X0),sK2) | v1_xboole_0(sK1)) ) | (~spl6_7 | ~spl6_9 | ~spl6_21)),
% 0.21/0.51    inference(forward_demodulation,[],[f573,f180])).
% 0.21/0.51  fof(f573,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~v1_funct_2(sK3,sK1,sK2) | m1_subset_1(k3_funct_2(sK1,sK2,sK3,X0),sK2) | v1_xboole_0(sK1)) ) | (~spl6_7 | ~spl6_9)),
% 0.21/0.51    inference(resolution,[],[f316,f109])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f108])).
% 0.21/0.51  fof(f316,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(X3,X4) | ~v1_funct_2(sK3,X4,X5) | m1_subset_1(k3_funct_2(X4,X5,sK3,X3),X5) | v1_xboole_0(X4)) ) | ~spl6_9),
% 0.21/0.51    inference(resolution,[],[f77,f117])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    v1_funct_1(sK3) | ~spl6_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f116])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 0.21/0.51  fof(f519,plain,(
% 0.21/0.51    spl6_65 | ~spl6_29 | ~spl6_42),
% 0.21/0.51    inference(avatar_split_clause,[],[f470,f307,f221,f496])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    spl6_29 <=> v1_funct_2(sK3,sK1,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.51  fof(f470,plain,(
% 0.21/0.51    v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | (~spl6_29 | ~spl6_42)),
% 0.21/0.51    inference(superposition,[],[f222,f308])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK1,k1_xboole_0) | ~spl6_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f221])).
% 0.21/0.51  fof(f425,plain,(
% 0.21/0.51    ~spl6_19 | ~spl6_46 | spl6_55),
% 0.21/0.51    inference(avatar_split_clause,[],[f422,f387,f333,f167])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    spl6_19 <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.51  fof(f333,plain,(
% 0.21/0.51    spl6_46 <=> ! [X2] : (r2_hidden(k1_funct_1(sK3,sK5),X2) | ~r1_tarski(k2_relat_1(sK3),X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.21/0.51  fof(f387,plain,(
% 0.21/0.51    spl6_55 <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 0.21/0.51  fof(f422,plain,(
% 0.21/0.51    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | (~spl6_46 | spl6_55)),
% 0.21/0.51    inference(resolution,[],[f388,f334])).
% 0.21/0.51  fof(f334,plain,(
% 0.21/0.51    ( ! [X2] : (r2_hidden(k1_funct_1(sK3,sK5),X2) | ~r1_tarski(k2_relat_1(sK3),X2)) ) | ~spl6_46),
% 0.21/0.51    inference(avatar_component_clause,[],[f333])).
% 0.21/0.51  fof(f388,plain,(
% 0.21/0.51    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | spl6_55),
% 0.21/0.51    inference(avatar_component_clause,[],[f387])).
% 0.21/0.51  fof(f408,plain,(
% 0.21/0.51    ~spl6_5 | spl6_54),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f406])).
% 0.21/0.51  fof(f406,plain,(
% 0.21/0.51    $false | (~spl6_5 | spl6_54)),
% 0.21/0.51    inference(subsumption_resolution,[],[f101,f404])).
% 0.21/0.51  fof(f404,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | spl6_54),
% 0.21/0.51    inference(resolution,[],[f385,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f385,plain,(
% 0.21/0.51    ~v5_relat_1(sK4,sK0) | spl6_54),
% 0.21/0.51    inference(avatar_component_clause,[],[f384])).
% 0.21/0.51  fof(f384,plain,(
% 0.21/0.51    spl6_54 <=> v5_relat_1(sK4,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl6_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl6_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.51  fof(f403,plain,(
% 0.21/0.51    spl6_56),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f401])).
% 0.21/0.51  fof(f401,plain,(
% 0.21/0.51    $false | spl6_56),
% 0.21/0.51    inference(resolution,[],[f395,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f395,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | spl6_56),
% 0.21/0.51    inference(avatar_component_clause,[],[f394])).
% 0.21/0.51  fof(f394,plain,(
% 0.21/0.51    spl6_56 <=> v1_relat_1(k2_zfmisc_1(sK2,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).
% 0.21/0.51  fof(f396,plain,(
% 0.21/0.51    ~spl6_56 | ~spl6_5 | spl6_53),
% 0.21/0.51    inference(avatar_split_clause,[],[f391,f381,f100,f394])).
% 0.21/0.51  fof(f381,plain,(
% 0.21/0.51    spl6_53 <=> v1_relat_1(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 0.21/0.51  fof(f391,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | (~spl6_5 | spl6_53)),
% 0.21/0.51    inference(resolution,[],[f390,f101])).
% 0.21/0.51  fof(f390,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_53),
% 0.21/0.51    inference(resolution,[],[f382,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f382,plain,(
% 0.21/0.51    ~v1_relat_1(sK4) | spl6_53),
% 0.21/0.51    inference(avatar_component_clause,[],[f381])).
% 0.21/0.51  fof(f389,plain,(
% 0.21/0.51    ~spl6_53 | ~spl6_54 | ~spl6_6 | ~spl6_55 | spl6_50),
% 0.21/0.51    inference(avatar_split_clause,[],[f379,f361,f387,f104,f384,f381])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl6_6 <=> v1_funct_1(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.51  fof(f361,plain,(
% 0.21/0.51    spl6_50 <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 0.21/0.51  fof(f379,plain,(
% 0.21/0.51    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,sK0) | ~v1_relat_1(sK4) | spl6_50),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f378])).
% 0.21/0.51  fof(f378,plain,(
% 0.21/0.51    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,sK0) | ~v1_relat_1(sK4) | spl6_50),
% 0.21/0.51    inference(superposition,[],[f362,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.21/0.51  fof(f362,plain,(
% 0.21/0.51    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl6_50),
% 0.21/0.51    inference(avatar_component_clause,[],[f361])).
% 0.21/0.51  fof(f364,plain,(
% 0.21/0.51    spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_4 | spl6_2 | ~spl6_50 | ~spl6_20 | spl6_1 | ~spl6_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f354,f157,f84,f171,f361,f88,f96,f100,f104,f108,f112,f116,f120])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    spl6_10 <=> v1_xboole_0(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    spl6_8 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl6_2 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    spl6_20 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl6_1 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    spl6_17 <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.51  fof(f354,plain,(
% 0.21/0.51    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_xboole_0(sK2) | (spl6_1 | ~spl6_17)),
% 0.21/0.51    inference(forward_demodulation,[],[f353,f158])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl6_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f157])).
% 0.21/0.51  fof(f353,plain,(
% 0.21/0.51    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_xboole_0(sK2) | spl6_1),
% 0.21/0.51    inference(superposition,[],[f85,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.21/0.51    inference(flattening,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) | spl6_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f84])).
% 0.21/0.51  fof(f335,plain,(
% 0.21/0.51    ~spl6_36 | spl6_46 | ~spl6_4 | ~spl6_45),
% 0.21/0.51    inference(avatar_split_clause,[],[f331,f324,f96,f333,f251])).
% 0.21/0.51  fof(f251,plain,(
% 0.21/0.51    spl6_36 <=> v1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.21/0.51  fof(f324,plain,(
% 0.21/0.51    spl6_45 <=> ! [X1,X0] : (~v5_relat_1(sK3,X0) | ~m1_subset_1(X1,sK1) | r2_hidden(k1_funct_1(sK3,X1),X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.21/0.51  % (3267)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  fof(f331,plain,(
% 0.21/0.51    ( ! [X2] : (r2_hidden(k1_funct_1(sK3,sK5),X2) | ~r1_tarski(k2_relat_1(sK3),X2) | ~v1_relat_1(sK3)) ) | (~spl6_4 | ~spl6_45)),
% 0.21/0.51    inference(resolution,[],[f329,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.51  fof(f329,plain,(
% 0.21/0.51    ( ! [X0] : (~v5_relat_1(sK3,X0) | r2_hidden(k1_funct_1(sK3,sK5),X0)) ) | (~spl6_4 | ~spl6_45)),
% 0.21/0.51    inference(resolution,[],[f325,f97])).
% 0.21/0.51  fof(f325,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,sK1) | ~v5_relat_1(sK3,X0) | r2_hidden(k1_funct_1(sK3,X1),X0)) ) | ~spl6_45),
% 0.21/0.51    inference(avatar_component_clause,[],[f324])).
% 0.21/0.51  fof(f328,plain,(
% 0.21/0.51    spl6_2 | ~spl6_44),
% 0.21/0.51    inference(avatar_split_clause,[],[f327,f321,f88])).
% 0.21/0.51  fof(f327,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl6_44),
% 0.21/0.51    inference(resolution,[],[f322,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.51  fof(f322,plain,(
% 0.21/0.51    v1_xboole_0(sK1) | ~spl6_44),
% 0.21/0.51    inference(avatar_component_clause,[],[f321])).
% 0.21/0.51  fof(f326,plain,(
% 0.21/0.51    spl6_44 | spl6_45 | ~spl6_37),
% 0.21/0.51    inference(avatar_split_clause,[],[f319,f255,f324,f321])).
% 0.21/0.51  fof(f255,plain,(
% 0.21/0.51    spl6_37 <=> ! [X1,X0] : (~r2_hidden(X0,sK1) | ~v5_relat_1(sK3,X1) | r2_hidden(k1_funct_1(sK3,X0),X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.21/0.51  fof(f319,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v5_relat_1(sK3,X0) | r2_hidden(k1_funct_1(sK3,X1),X0) | v1_xboole_0(sK1) | ~m1_subset_1(X1,sK1)) ) | ~spl6_37),
% 0.21/0.51    inference(resolution,[],[f256,f63])).
% 0.21/0.51  fof(f256,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~v5_relat_1(sK3,X1) | r2_hidden(k1_funct_1(sK3,X0),X1)) ) | ~spl6_37),
% 0.21/0.51    inference(avatar_component_clause,[],[f255])).
% 0.21/0.51  fof(f310,plain,(
% 0.21/0.51    spl6_42 | spl6_2 | ~spl6_29 | ~spl6_28),
% 0.21/0.51    inference(avatar_split_clause,[],[f303,f217,f221,f88,f307])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    spl6_28 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.51  fof(f303,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,sK1,k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK3 | ~spl6_28),
% 0.21/0.51    inference(resolution,[],[f218,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.21/0.51    inference(equality_resolution,[],[f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~spl6_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f217])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    spl6_38),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f264])).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    $false | spl6_38),
% 0.21/0.51    inference(resolution,[],[f262,f60])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | spl6_38),
% 0.21/0.51    inference(avatar_component_clause,[],[f261])).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    spl6_38 <=> v1_relat_1(k2_zfmisc_1(sK1,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.21/0.51  fof(f263,plain,(
% 0.21/0.51    ~spl6_38 | ~spl6_7 | spl6_36),
% 0.21/0.51    inference(avatar_split_clause,[],[f259,f251,f108,f261])).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | (~spl6_7 | spl6_36)),
% 0.21/0.51    inference(resolution,[],[f258,f109])).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_36),
% 0.21/0.51    inference(resolution,[],[f252,f58])).
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    ~v1_relat_1(sK3) | spl6_36),
% 0.21/0.51    inference(avatar_component_clause,[],[f251])).
% 0.21/0.51  fof(f257,plain,(
% 0.21/0.51    ~spl6_36 | ~spl6_9 | spl6_37 | ~spl6_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f249,f182,f255,f116,f251])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    spl6_22 <=> sK1 = k1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.51  fof(f249,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),X1) | ~v1_funct_1(sK3) | ~v5_relat_1(sK3,X1) | ~v1_relat_1(sK3)) ) | ~spl6_22),
% 0.21/0.51    inference(superposition,[],[f64,f183])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    sK1 = k1_relat_1(sK3) | ~spl6_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f182])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X2),X0) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 0.21/0.51  fof(f227,plain,(
% 0.21/0.51    ~spl6_30 | spl6_10 | ~spl6_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f196,f179,f120,f225])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    ~v1_xboole_0(k1_xboole_0) | (spl6_10 | ~spl6_21)),
% 0.21/0.51    inference(superposition,[],[f121,f180])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    ~v1_xboole_0(sK2) | spl6_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f120])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    spl6_29 | ~spl6_8 | ~spl6_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f195,f179,f112,f221])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK1,k1_xboole_0) | (~spl6_8 | ~spl6_21)),
% 0.21/0.51    inference(superposition,[],[f113,f180])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK1,sK2) | ~spl6_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f112])).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    spl6_28 | ~spl6_7 | ~spl6_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f194,f179,f108,f217])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl6_7 | ~spl6_21)),
% 0.21/0.51    inference(superposition,[],[f109,f180])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ~spl6_7 | spl6_21 | spl6_22 | ~spl6_8 | ~spl6_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f177,f161,f112,f182,f179,f108])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    spl6_18 <=> k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_8 | ~spl6_18)),
% 0.21/0.51    inference(forward_demodulation,[],[f176,f162])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) | ~spl6_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f161])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_8),
% 0.21/0.51    inference(resolution,[],[f71,f113])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    spl6_20 | ~spl6_3 | ~spl6_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f165,f157,f92,f171])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl6_3 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | (~spl6_3 | ~spl6_17)),
% 0.21/0.51    inference(superposition,[],[f93,f158])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl6_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f92])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    spl6_19 | ~spl6_16 | ~spl6_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f164,f157,f151,f167])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    spl6_16 <=> r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | (~spl6_16 | ~spl6_17)),
% 0.21/0.51    inference(superposition,[],[f152,f158])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl6_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f151])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    spl6_18 | ~spl6_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f155,f108,f161])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) | ~spl6_7),
% 0.21/0.51    inference(resolution,[],[f69,f109])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    spl6_17 | ~spl6_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f154,f100,f157])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl6_5),
% 0.21/0.51    inference(resolution,[],[f69,f101])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ~spl6_7 | spl6_16 | ~spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f148,f92,f151,f108])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_3),
% 0.21/0.51    inference(superposition,[],[f93,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ~spl6_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f47,f120])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ~v1_xboole_0(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f43,f42,f41,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) => (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f16])).
% 0.21/0.51  fof(f16,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    spl6_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f116])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl6_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f49,f112])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl6_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f50,f108])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    spl6_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f51,f104])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    v1_funct_1(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    spl6_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f52,f100])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    spl6_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f53,f96])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    m1_subset_1(sK5,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f54,f92])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ~spl6_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f55,f88])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ~spl6_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f56,f84])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (3265)------------------------------
% 0.21/0.51  % (3265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3265)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (3265)Memory used [KB]: 11129
% 0.21/0.51  % (3265)Time elapsed: 0.039 s
% 0.21/0.51  % (3265)------------------------------
% 0.21/0.51  % (3265)------------------------------
% 0.21/0.51  % (3256)Success in time 0.151 s
%------------------------------------------------------------------------------

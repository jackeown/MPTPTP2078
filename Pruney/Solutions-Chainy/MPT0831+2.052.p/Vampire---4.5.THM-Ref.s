%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 168 expanded)
%              Number of leaves         :   29 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  274 ( 398 expanded)
%              Number of equality atoms :   30 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f318,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f77,f84,f109,f118,f125,f133,f139,f146,f157,f187,f232,f251,f274,f317])).

fof(f317,plain,
    ( ~ spl4_8
    | ~ spl4_13
    | spl4_15
    | ~ spl4_29 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_13
    | spl4_15
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f310,f108])).

fof(f108,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_8
  <=> r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f310,plain,
    ( ~ r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl4_13
    | spl4_15
    | ~ spl4_29 ),
    inference(backward_demodulation,[],[f156,f281])).

fof(f281,plain,
    ( sK3 = k7_relat_1(sK3,sK2)
    | ~ spl4_13
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f279,f145])).

fof(f145,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_13
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f279,plain,
    ( sK3 = k7_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_29 ),
    inference(resolution,[],[f273,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

% (3358)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f273,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl4_29
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f156,plain,
    ( ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl4_15
  <=> r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f274,plain,
    ( spl4_29
    | ~ spl4_4
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f260,f244,f74,f271])).

fof(f74,plain,
    ( spl4_4
  <=> sK2 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f244,plain,
    ( spl4_27
  <=> ! [X0] : v4_relat_1(sK3,k2_xboole_0(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f260,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl4_4
    | ~ spl4_27 ),
    inference(superposition,[],[f245,f76])).

fof(f76,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f245,plain,
    ( ! [X0] : v4_relat_1(sK3,k2_xboole_0(sK1,X0))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f244])).

fof(f251,plain,
    ( spl4_27
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f240,f230,f244])).

fof(f230,plain,
    ( spl4_25
  <=> ! [X0] : v4_relat_1(sK3,k2_xboole_0(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f240,plain,
    ( ! [X1] : v4_relat_1(sK3,k2_xboole_0(sK1,X1))
    | ~ spl4_25 ),
    inference(superposition,[],[f231,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f231,plain,
    ( ! [X0] : v4_relat_1(sK3,k2_xboole_0(X0,sK1))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f230])).

fof(f232,plain,
    ( spl4_25
    | ~ spl4_13
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f223,f185,f143,f230])).

fof(f185,plain,
    ( spl4_19
  <=> ! [X0] : r1_tarski(k1_relat_1(sK3),k2_xboole_0(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f223,plain,
    ( ! [X0] : v4_relat_1(sK3,k2_xboole_0(X0,sK1))
    | ~ spl4_13
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f218,f145])).

fof(f218,plain,
    ( ! [X0] :
        ( v4_relat_1(sK3,k2_xboole_0(X0,sK1))
        | ~ v1_relat_1(sK3) )
    | ~ spl4_19 ),
    inference(resolution,[],[f186,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f186,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(sK3),k2_xboole_0(X0,sK1))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f185])).

fof(f187,plain,
    ( spl4_19
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f159,f136,f185])).

fof(f136,plain,
    ( spl4_12
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f159,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(sK3),k2_xboole_0(X0,sK1))
    | ~ spl4_12 ),
    inference(resolution,[],[f138,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f138,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f157,plain,
    ( ~ spl4_15
    | ~ spl4_2
    | spl4_5 ),
    inference(avatar_split_clause,[],[f147,f81,f59,f154])).

fof(f59,plain,
    ( spl4_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f81,plain,
    ( spl4_5
  <=> r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f147,plain,
    ( ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)
    | ~ spl4_2
    | spl4_5 ),
    inference(backward_demodulation,[],[f83,f119])).

fof(f119,plain,
    ( ! [X0] : k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl4_2 ),
    inference(resolution,[],[f48,f61])).

fof(f61,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f83,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f146,plain,
    ( spl4_13
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f140,f59,f143])).

fof(f140,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f70,f61])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f36,f37])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f139,plain,
    ( spl4_12
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f134,f130,f136])).

fof(f130,plain,
    ( spl4_11
  <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f134,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ spl4_11 ),
    inference(resolution,[],[f132,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f132,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f130])).

fof(f133,plain,
    ( spl4_11
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f128,f122,f115,f130])).

fof(f115,plain,
    ( spl4_9
  <=> k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f122,plain,
    ( spl4_10
  <=> m1_subset_1(k1_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f128,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f124,f117])).

fof(f117,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f124,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f125,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f112,f59,f122])).

fof(f112,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f47,f61])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f118,plain,
    ( spl4_9
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f110,f59,f115])).

fof(f110,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f46,f61])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f109,plain,
    ( spl4_8
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f103,f59,f106])).

fof(f103,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f52,f61])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f84,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f35,f81])).

fof(f35,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

fof(f77,plain,
    ( spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f71,f54,f74])).

fof(f54,plain,
    ( spl4_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f71,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f41,f56])).

fof(f56,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f62,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f33,f59])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f34,f54])).

fof(f34,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:00:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (3351)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (3355)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (3363)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (3354)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (3353)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (3366)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (3371)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (3364)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (3352)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (3351)Refutation not found, incomplete strategy% (3351)------------------------------
% 0.21/0.52  % (3351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3351)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (3351)Memory used [KB]: 10618
% 0.21/0.52  % (3351)Time elapsed: 0.102 s
% 0.21/0.52  % (3351)------------------------------
% 0.21/0.52  % (3351)------------------------------
% 0.21/0.52  % (3369)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (3367)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (3352)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f318,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f57,f62,f77,f84,f109,f118,f125,f133,f139,f146,f157,f187,f232,f251,f274,f317])).
% 0.21/0.52  fof(f317,plain,(
% 0.21/0.52    ~spl4_8 | ~spl4_13 | spl4_15 | ~spl4_29),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f316])).
% 0.21/0.52  fof(f316,plain,(
% 0.21/0.52    $false | (~spl4_8 | ~spl4_13 | spl4_15 | ~spl4_29)),
% 0.21/0.52    inference(subsumption_resolution,[],[f310,f108])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    r2_relset_1(sK1,sK0,sK3,sK3) | ~spl4_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl4_8 <=> r2_relset_1(sK1,sK0,sK3,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.52  fof(f310,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,sK0,sK3,sK3) | (~spl4_13 | spl4_15 | ~spl4_29)),
% 0.21/0.52    inference(backward_demodulation,[],[f156,f281])).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    sK3 = k7_relat_1(sK3,sK2) | (~spl4_13 | ~spl4_29)),
% 0.21/0.52    inference(subsumption_resolution,[],[f279,f145])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    v1_relat_1(sK3) | ~spl4_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f143])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    spl4_13 <=> v1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.52  fof(f279,plain,(
% 0.21/0.52    sK3 = k7_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | ~spl4_29),
% 0.21/0.52    inference(resolution,[],[f273,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  % (3358)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.52  fof(f273,plain,(
% 0.21/0.52    v4_relat_1(sK3,sK2) | ~spl4_29),
% 0.21/0.52    inference(avatar_component_clause,[],[f271])).
% 0.21/0.52  fof(f271,plain,(
% 0.21/0.52    spl4_29 <=> v4_relat_1(sK3,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) | spl4_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f154])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    spl4_15 <=> r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    spl4_29 | ~spl4_4 | ~spl4_27),
% 0.21/0.52    inference(avatar_split_clause,[],[f260,f244,f74,f271])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl4_4 <=> sK2 = k2_xboole_0(sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    spl4_27 <=> ! [X0] : v4_relat_1(sK3,k2_xboole_0(sK1,X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.52  fof(f260,plain,(
% 0.21/0.52    v4_relat_1(sK3,sK2) | (~spl4_4 | ~spl4_27)),
% 0.21/0.52    inference(superposition,[],[f245,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    sK2 = k2_xboole_0(sK1,sK2) | ~spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f74])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    ( ! [X0] : (v4_relat_1(sK3,k2_xboole_0(sK1,X0))) ) | ~spl4_27),
% 0.21/0.52    inference(avatar_component_clause,[],[f244])).
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    spl4_27 | ~spl4_25),
% 0.21/0.52    inference(avatar_split_clause,[],[f240,f230,f244])).
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    spl4_25 <=> ! [X0] : v4_relat_1(sK3,k2_xboole_0(X0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    ( ! [X1] : (v4_relat_1(sK3,k2_xboole_0(sK1,X1))) ) | ~spl4_25),
% 0.21/0.52    inference(superposition,[],[f231,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    ( ! [X0] : (v4_relat_1(sK3,k2_xboole_0(X0,sK1))) ) | ~spl4_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f230])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    spl4_25 | ~spl4_13 | ~spl4_19),
% 0.21/0.52    inference(avatar_split_clause,[],[f223,f185,f143,f230])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    spl4_19 <=> ! [X0] : r1_tarski(k1_relat_1(sK3),k2_xboole_0(X0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    ( ! [X0] : (v4_relat_1(sK3,k2_xboole_0(X0,sK1))) ) | (~spl4_13 | ~spl4_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f218,f145])).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    ( ! [X0] : (v4_relat_1(sK3,k2_xboole_0(X0,sK1)) | ~v1_relat_1(sK3)) ) | ~spl4_19),
% 0.21/0.52    inference(resolution,[],[f186,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_relat_1(sK3),k2_xboole_0(X0,sK1))) ) | ~spl4_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f185])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    spl4_19 | ~spl4_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f159,f136,f185])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    spl4_12 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_relat_1(sK3),k2_xboole_0(X0,sK1))) ) | ~spl4_12),
% 0.21/0.52    inference(resolution,[],[f138,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    r1_tarski(k1_relat_1(sK3),sK1) | ~spl4_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f136])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    ~spl4_15 | ~spl4_2 | spl4_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f147,f81,f59,f154])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    spl4_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl4_5 <=> r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) | (~spl4_2 | spl4_5)),
% 0.21/0.52    inference(backward_demodulation,[],[f83,f119])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ( ! [X0] : (k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0)) ) | ~spl4_2),
% 0.21/0.52    inference(resolution,[],[f48,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f59])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) | spl4_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f81])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    spl4_13 | ~spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f140,f59,f143])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    v1_relat_1(sK3) | ~spl4_2),
% 0.21/0.52    inference(resolution,[],[f70,f61])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f36,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    spl4_12 | ~spl4_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f134,f130,f136])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    spl4_11 <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    r1_tarski(k1_relat_1(sK3),sK1) | ~spl4_11),
% 0.21/0.52    inference(resolution,[],[f132,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) | ~spl4_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f130])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    spl4_11 | ~spl4_9 | ~spl4_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f128,f122,f115,f130])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    spl4_9 <=> k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    spl4_10 <=> m1_subset_1(k1_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) | (~spl4_9 | ~spl4_10)),
% 0.21/0.52    inference(forward_demodulation,[],[f124,f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) | ~spl4_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f115])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    m1_subset_1(k1_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK1)) | ~spl4_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f122])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    spl4_10 | ~spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f112,f59,f122])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    m1_subset_1(k1_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK1)) | ~spl4_2),
% 0.21/0.52    inference(resolution,[],[f47,f61])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl4_9 | ~spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f110,f59,f115])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) | ~spl4_2),
% 0.21/0.52    inference(resolution,[],[f46,f61])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    spl4_8 | ~spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f103,f59,f106])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    r2_relset_1(sK1,sK0,sK3,sK3) | ~spl4_2),
% 0.21/0.52    inference(resolution,[],[f52,f61])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ~spl4_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f35,f81])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.21/0.52    inference(negated_conjecture,[],[f13])).
% 0.21/0.52  fof(f13,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl4_4 | ~spl4_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f71,f54,f74])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl4_1 <=> r1_tarski(sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    sK2 = k2_xboole_0(sK1,sK2) | ~spl4_1),
% 0.21/0.52    inference(resolution,[],[f41,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2) | ~spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f54])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f33,f59])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    spl4_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f34,f54])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (3352)------------------------------
% 0.21/0.52  % (3352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3352)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (3352)Memory used [KB]: 6268
% 0.21/0.52  % (3352)Time elapsed: 0.106 s
% 0.21/0.52  % (3352)------------------------------
% 0.21/0.52  % (3352)------------------------------
% 0.21/0.52  % (3349)Success in time 0.161 s
%------------------------------------------------------------------------------

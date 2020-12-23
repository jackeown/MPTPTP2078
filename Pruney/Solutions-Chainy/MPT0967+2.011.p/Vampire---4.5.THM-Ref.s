%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 286 expanded)
%              Number of leaves         :   18 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :  309 (1194 expanded)
%              Number of equality atoms :   71 ( 335 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f797,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f123,f146,f238,f330,f334,f442,f736])).

fof(f736,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f727])).

fof(f727,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f583,f529,f638,f62])).

fof(f62,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f638,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f549,f637])).

fof(f637,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f545,f632])).

fof(f632,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f492,f529,f61])).

fof(f61,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f492,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f467,f82])).

fof(f82,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f467,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f31,f85])).

fof(f85,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f31,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(f545,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f544,f82])).

fof(f544,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f98,f85])).

fof(f98,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f32,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f549,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f241,f82])).

fof(f241,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f136,f52])).

fof(f136,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f529,plain,
    ( ! [X0] : m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f510,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f510,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f507,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f507,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f46,f479,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f479,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f468,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f468,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f32,f85])).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f583,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ spl5_1
    | spl5_6 ),
    inference(forward_demodulation,[],[f141,f82])).

fof(f141,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl5_6
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f442,plain,
    ( spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f86,f385])).

fof(f385,plain,
    ( k1_xboole_0 = sK1
    | spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | spl5_6 ),
    inference(forward_demodulation,[],[f118,f257])).

fof(f257,plain,
    ( k1_xboole_0 = sK2
    | spl5_2
    | ~ spl5_5
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f141,f136,f245,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f245,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | spl5_2
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f241,f103])).

fof(f103,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl5_2 ),
    inference(forward_demodulation,[],[f98,f99])).

fof(f99,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f86,f31,f32,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f118,plain,
    ( sK1 = sK2
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_3
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f86,plain,
    ( k1_xboole_0 != sK1
    | spl5_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f334,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f30,f145])).

fof(f145,plain,
    ( ~ v1_funct_1(sK3)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl5_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f330,plain,
    ( spl5_2
    | spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl5_2
    | spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f46,f285])).

fof(f285,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_2
    | spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(backward_demodulation,[],[f212,f257])).

fof(f212,plain,
    ( ~ v1_xboole_0(sK2)
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f59,f195])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ r1_tarski(sK2,X0) )
    | spl5_4 ),
    inference(resolution,[],[f151,f50])).

fof(f151,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) )
    | spl5_4 ),
    inference(resolution,[],[f124,f53])).

fof(f124,plain,
    ( r2_hidden(sK4(sK2,sK1),sK2)
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f122,f55])).

fof(f122,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_4
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f238,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f100,f170,f71,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f71,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f33,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f33,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f170,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f137,f50])).

fof(f137,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f100,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f32,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f146,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f28,f143,f139,f135])).

fof(f28,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f123,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f75,f120,f116])).

fof(f75,plain,
    ( ~ r1_tarski(sK2,sK1)
    | sK1 = sK2 ),
    inference(resolution,[],[f33,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f87,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f29,f84,f80])).

fof(f29,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (28359)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (28365)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (28369)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (28360)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (28361)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (28374)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (28358)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (28350)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (28353)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (28366)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (28347)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (28373)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (28349)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (28370)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (28364)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (28352)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (28354)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (28351)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (28348)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (28375)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (28371)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (28363)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (28362)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (28376)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (28372)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (28367)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (28356)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (28355)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (28355)Refutation not found, incomplete strategy% (28355)------------------------------
% 0.20/0.55  % (28355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (28355)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (28355)Memory used [KB]: 10874
% 0.20/0.55  % (28355)Time elapsed: 0.140 s
% 0.20/0.55  % (28355)------------------------------
% 0.20/0.55  % (28355)------------------------------
% 0.20/0.55  % (28368)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (28357)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (28351)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f797,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f87,f123,f146,f238,f330,f334,f442,f736])).
% 0.20/0.56  fof(f736,plain,(
% 0.20/0.56    ~spl5_1 | ~spl5_2 | ~spl5_5 | spl5_6),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f727])).
% 0.20/0.56  fof(f727,plain,(
% 0.20/0.56    $false | (~spl5_1 | ~spl5_2 | ~spl5_5 | spl5_6)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f583,f529,f638,f62])).
% 0.20/0.56  fof(f62,plain,(
% 0.20/0.56    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.56    inference(equality_resolution,[],[f42])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(flattening,[],[f20])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(ennf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.56  fof(f638,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3) | (~spl5_1 | ~spl5_2 | ~spl5_5)),
% 0.20/0.56    inference(backward_demodulation,[],[f549,f637])).
% 0.20/0.56  fof(f637,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relat_1(sK3) | (~spl5_1 | ~spl5_2)),
% 0.20/0.56    inference(backward_demodulation,[],[f545,f632])).
% 0.20/0.56  fof(f632,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl5_1 | ~spl5_2)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f492,f529,f61])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.56    inference(equality_resolution,[],[f43])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f21])).
% 0.20/0.56  fof(f492,plain,(
% 0.20/0.56    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl5_1 | ~spl5_2)),
% 0.20/0.56    inference(backward_demodulation,[],[f467,f82])).
% 0.20/0.56  fof(f82,plain,(
% 0.20/0.56    k1_xboole_0 = sK0 | ~spl5_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f80])).
% 0.20/0.56  fof(f80,plain,(
% 0.20/0.56    spl5_1 <=> k1_xboole_0 = sK0),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.56  fof(f467,plain,(
% 0.20/0.56    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl5_2),
% 0.20/0.56    inference(backward_demodulation,[],[f31,f85])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    k1_xboole_0 = sK1 | ~spl5_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f84])).
% 0.20/0.56  fof(f84,plain,(
% 0.20/0.56    spl5_2 <=> k1_xboole_0 = sK1),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.56    inference(flattening,[],[f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.56    inference(ennf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.56    inference(negated_conjecture,[],[f16])).
% 0.20/0.56  fof(f16,conjecture,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).
% 0.20/0.56  fof(f545,plain,(
% 0.20/0.56    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl5_1 | ~spl5_2)),
% 0.20/0.56    inference(forward_demodulation,[],[f544,f82])).
% 0.20/0.56  fof(f544,plain,(
% 0.20/0.56    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) | ~spl5_2),
% 0.20/0.56    inference(forward_demodulation,[],[f98,f85])).
% 0.20/0.56  fof(f98,plain,(
% 0.20/0.56    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f32,f52])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(ennf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.56    inference(cnf_transformation,[],[f19])).
% 0.20/0.56  fof(f549,plain,(
% 0.20/0.56    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK2,sK3) | (~spl5_1 | ~spl5_5)),
% 0.20/0.56    inference(forward_demodulation,[],[f241,f82])).
% 0.20/0.56  fof(f241,plain,(
% 0.20/0.56    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | ~spl5_5),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f136,f52])).
% 0.20/0.56  fof(f136,plain,(
% 0.20/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl5_5),
% 0.20/0.56    inference(avatar_component_clause,[],[f135])).
% 0.20/0.56  fof(f135,plain,(
% 0.20/0.56    spl5_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.56  fof(f529,plain,(
% 0.20/0.56    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(X0))) ) | ~spl5_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f510,f50])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.56  fof(f510,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(sK3,X0)) ) | ~spl5_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f507,f55])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.57  fof(f507,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl5_2),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f46,f479,f53])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.57  fof(f479,plain,(
% 0.20/0.57    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl5_2),
% 0.20/0.57    inference(forward_demodulation,[],[f468,f57])).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.57    inference(equality_resolution,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.57  fof(f468,plain,(
% 0.20/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl5_2),
% 0.20/0.57    inference(backward_demodulation,[],[f32,f85])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    v1_xboole_0(k1_xboole_0)),
% 0.20/0.57    inference(cnf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    v1_xboole_0(k1_xboole_0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.57  fof(f583,plain,(
% 0.20/0.57    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (~spl5_1 | spl5_6)),
% 0.20/0.57    inference(forward_demodulation,[],[f141,f82])).
% 0.20/0.57  fof(f141,plain,(
% 0.20/0.57    ~v1_funct_2(sK3,sK0,sK2) | spl5_6),
% 0.20/0.57    inference(avatar_component_clause,[],[f139])).
% 0.20/0.57  fof(f139,plain,(
% 0.20/0.57    spl5_6 <=> v1_funct_2(sK3,sK0,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.57  fof(f442,plain,(
% 0.20/0.57    spl5_2 | ~spl5_3 | ~spl5_5 | spl5_6),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f438])).
% 0.20/0.57  fof(f438,plain,(
% 0.20/0.57    $false | (spl5_2 | ~spl5_3 | ~spl5_5 | spl5_6)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f86,f385])).
% 0.20/0.57  fof(f385,plain,(
% 0.20/0.57    k1_xboole_0 = sK1 | (spl5_2 | ~spl5_3 | ~spl5_5 | spl5_6)),
% 0.20/0.57    inference(forward_demodulation,[],[f118,f257])).
% 0.20/0.57  fof(f257,plain,(
% 0.20/0.57    k1_xboole_0 = sK2 | (spl5_2 | ~spl5_5 | spl5_6)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f141,f136,f245,f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f21])).
% 0.20/0.57  fof(f245,plain,(
% 0.20/0.57    sK0 = k1_relset_1(sK0,sK2,sK3) | (spl5_2 | ~spl5_5)),
% 0.20/0.57    inference(forward_demodulation,[],[f241,f103])).
% 0.20/0.57  fof(f103,plain,(
% 0.20/0.57    sK0 = k1_relat_1(sK3) | spl5_2),
% 0.20/0.57    inference(forward_demodulation,[],[f98,f99])).
% 0.20/0.57  fof(f99,plain,(
% 0.20/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | spl5_2),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f86,f31,f32,f45])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f21])).
% 0.20/0.57  fof(f118,plain,(
% 0.20/0.57    sK1 = sK2 | ~spl5_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f116])).
% 0.20/0.57  fof(f116,plain,(
% 0.20/0.57    spl5_3 <=> sK1 = sK2),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.57  fof(f86,plain,(
% 0.20/0.57    k1_xboole_0 != sK1 | spl5_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f84])).
% 0.20/0.57  fof(f334,plain,(
% 0.20/0.57    spl5_7),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f331])).
% 0.20/0.57  fof(f331,plain,(
% 0.20/0.57    $false | spl5_7),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f30,f145])).
% 0.20/0.57  fof(f145,plain,(
% 0.20/0.57    ~v1_funct_1(sK3) | spl5_7),
% 0.20/0.57    inference(avatar_component_clause,[],[f143])).
% 0.20/0.57  fof(f143,plain,(
% 0.20/0.57    spl5_7 <=> v1_funct_1(sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    v1_funct_1(sK3)),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f330,plain,(
% 0.20/0.57    spl5_2 | spl5_4 | ~spl5_5 | spl5_6),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f327])).
% 0.20/0.57  fof(f327,plain,(
% 0.20/0.57    $false | (spl5_2 | spl5_4 | ~spl5_5 | spl5_6)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f46,f285])).
% 0.20/0.57  fof(f285,plain,(
% 0.20/0.57    ~v1_xboole_0(k1_xboole_0) | (spl5_2 | spl5_4 | ~spl5_5 | spl5_6)),
% 0.20/0.57    inference(backward_demodulation,[],[f212,f257])).
% 0.20/0.57  fof(f212,plain,(
% 0.20/0.57    ~v1_xboole_0(sK2) | spl5_4),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f59,f195])).
% 0.20/0.57  fof(f195,plain,(
% 0.20/0.57    ( ! [X0] : (~v1_xboole_0(X0) | ~r1_tarski(sK2,X0)) ) | spl5_4),
% 0.20/0.57    inference(resolution,[],[f151,f50])).
% 0.20/0.57  fof(f151,plain,(
% 0.20/0.57    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1)) ) | spl5_4),
% 0.20/0.57    inference(resolution,[],[f124,f53])).
% 0.20/0.57  fof(f124,plain,(
% 0.20/0.57    r2_hidden(sK4(sK2,sK1),sK2) | spl5_4),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f122,f55])).
% 0.20/0.57  fof(f122,plain,(
% 0.20/0.57    ~r1_tarski(sK2,sK1) | spl5_4),
% 0.20/0.57    inference(avatar_component_clause,[],[f120])).
% 0.20/0.57  fof(f120,plain,(
% 0.20/0.57    spl5_4 <=> r1_tarski(sK2,sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.57    inference(equality_resolution,[],[f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.57  fof(f238,plain,(
% 0.20/0.57    spl5_5),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f229])).
% 0.20/0.57  fof(f229,plain,(
% 0.20/0.57    $false | spl5_5),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f100,f170,f71,f47])).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f23])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.57    inference(flattening,[],[f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.57  fof(f71,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X0,sK2))) )),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f33,f49])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    r1_tarski(sK1,sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f170,plain,(
% 0.20/0.57    ~r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) | spl5_5),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f137,f50])).
% 0.20/0.57  fof(f137,plain,(
% 0.20/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_5),
% 0.20/0.57    inference(avatar_component_clause,[],[f135])).
% 0.20/0.57  fof(f100,plain,(
% 0.20/0.57    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f32,f51])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f9])).
% 0.20/0.57  fof(f146,plain,(
% 0.20/0.57    ~spl5_5 | ~spl5_6 | ~spl5_7),
% 0.20/0.57    inference(avatar_split_clause,[],[f28,f143,f139,f135])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f123,plain,(
% 0.20/0.57    spl5_3 | ~spl5_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f75,f120,f116])).
% 0.20/0.57  fof(f75,plain,(
% 0.20/0.57    ~r1_tarski(sK2,sK1) | sK1 = sK2),
% 0.20/0.57    inference(resolution,[],[f33,f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f3])).
% 0.20/0.57  fof(f87,plain,(
% 0.20/0.57    spl5_1 | ~spl5_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f29,f84,f80])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (28351)------------------------------
% 0.20/0.57  % (28351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (28351)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (28351)Memory used [KB]: 6396
% 0.20/0.57  % (28351)Time elapsed: 0.140 s
% 0.20/0.57  % (28351)------------------------------
% 0.20/0.57  % (28351)------------------------------
% 0.20/0.57  % (28346)Success in time 0.216 s
%------------------------------------------------------------------------------

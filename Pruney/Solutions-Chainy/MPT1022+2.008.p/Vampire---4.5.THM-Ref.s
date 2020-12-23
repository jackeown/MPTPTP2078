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
% DateTime   : Thu Dec  3 13:06:04 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 282 expanded)
%              Number of leaves         :   19 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  269 (1214 expanded)
%              Number of equality atoms :   77 ( 324 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f140,f170,f174,f228,f281])).

fof(f281,plain,
    ( spl3_2
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | spl3_2
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f47,f256])).

fof(f256,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl3_2
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f151,f169])).

fof(f169,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl3_7
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f151,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK2))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f43,f89,f94,f150,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f150,plain,
    ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(superposition,[],[f113,f88])).

fof(f88,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0) ),
    inference(unit_resulting_resolution,[],[f46,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

fof(f113,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_2
  <=> sK1 = k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f94,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f54,f46,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f89,plain,(
    v2_funct_1(sK2) ),
    inference(unit_resulting_resolution,[],[f43,f45,f46,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f45,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f228,plain,
    ( spl3_2
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | spl3_2
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f69,f202])).

fof(f202,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK2))
    | spl3_2
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f151,f198])).

fof(f198,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f69,f178,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f178,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f47,f165])).

fof(f165,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl3_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f69,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f174,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f44,f161])).

fof(f161,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f44,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f170,plain,
    ( ~ spl3_5
    | spl3_6
    | spl3_7 ),
    inference(avatar_split_clause,[],[f105,f167,f163,f159])).

fof(f105,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK2,sK0,sK0) ),
    inference(forward_demodulation,[],[f98,f91])).

fof(f91,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f46,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f98,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_2(sK2,sK0,sK0) ),
    inference(resolution,[],[f46,f62])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f140,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f47,f136])).

fof(f136,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl3_1 ),
    inference(forward_demodulation,[],[f135,f127])).

fof(f127,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f94,f90,f93,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f93,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f46,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f90,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f43,f45,f46,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f135,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f43,f94,f109,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f109,plain,
    ( sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_1
  <=> sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f114,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f104,f111,f107])).

fof(f104,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))
    | sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f103,f87])).

fof(f87,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK0,sK2,X0) ),
    inference(unit_resulting_resolution,[],[f46,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f103,plain,
    ( sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(backward_demodulation,[],[f102,f87])).

fof(f102,plain,
    ( sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1))
    | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(backward_demodulation,[],[f42,f88])).

fof(f42,plain,
    ( sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))
    | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:41:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (21046)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.49  % (21059)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (21073)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.50  % (21048)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (21047)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (21057)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (21058)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (21057)Refutation not found, incomplete strategy% (21057)------------------------------
% 0.20/0.51  % (21057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21057)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (21057)Memory used [KB]: 10746
% 0.20/0.51  % (21057)Time elapsed: 0.108 s
% 0.20/0.51  % (21057)------------------------------
% 0.20/0.51  % (21057)------------------------------
% 0.20/0.51  % (21061)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (21068)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (21065)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (21060)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (21071)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.52  % (21052)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.52  % (21063)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.52  % (21054)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.52  % (21049)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.53  % (21050)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.53  % (21051)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.53  % (21050)Refutation found. Thanks to Tanya!
% 1.35/0.53  % SZS status Theorem for theBenchmark
% 1.35/0.53  % (21053)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.53  % SZS output start Proof for theBenchmark
% 1.35/0.53  fof(f282,plain,(
% 1.35/0.53    $false),
% 1.35/0.53    inference(avatar_sat_refutation,[],[f114,f140,f170,f174,f228,f281])).
% 1.35/0.53  fof(f281,plain,(
% 1.35/0.53    spl3_2 | ~spl3_7),
% 1.35/0.53    inference(avatar_contradiction_clause,[],[f278])).
% 1.35/0.53  fof(f278,plain,(
% 1.35/0.53    $false | (spl3_2 | ~spl3_7)),
% 1.35/0.53    inference(unit_resulting_resolution,[],[f47,f256])).
% 1.35/0.53  fof(f256,plain,(
% 1.35/0.53    ~r1_tarski(sK1,sK0) | (spl3_2 | ~spl3_7)),
% 1.35/0.53    inference(forward_demodulation,[],[f151,f169])).
% 1.35/0.53  fof(f169,plain,(
% 1.35/0.53    sK0 = k1_relat_1(sK2) | ~spl3_7),
% 1.35/0.53    inference(avatar_component_clause,[],[f167])).
% 1.35/0.53  fof(f167,plain,(
% 1.35/0.53    spl3_7 <=> sK0 = k1_relat_1(sK2)),
% 1.35/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.35/0.53  fof(f151,plain,(
% 1.35/0.53    ~r1_tarski(sK1,k1_relat_1(sK2)) | spl3_2),
% 1.35/0.53    inference(unit_resulting_resolution,[],[f43,f89,f94,f150,f64])).
% 1.35/0.53  fof(f64,plain,(
% 1.35/0.53    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0) )),
% 1.35/0.53    inference(cnf_transformation,[],[f34])).
% 1.35/0.53  fof(f34,plain,(
% 1.35/0.53    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.35/0.53    inference(flattening,[],[f33])).
% 1.35/0.53  fof(f33,plain,(
% 1.35/0.53    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.35/0.53    inference(ennf_transformation,[],[f11])).
% 1.35/0.53  fof(f11,axiom,(
% 1.35/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 1.35/0.53  fof(f150,plain,(
% 1.35/0.53    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | spl3_2),
% 1.35/0.53    inference(superposition,[],[f113,f88])).
% 1.35/0.53  fof(f88,plain,(
% 1.35/0.53    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0)) )),
% 1.35/0.53    inference(unit_resulting_resolution,[],[f46,f52])).
% 1.35/0.53  fof(f52,plain,(
% 1.35/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.35/0.53    inference(cnf_transformation,[],[f25])).
% 1.35/0.53  fof(f25,plain,(
% 1.35/0.53    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.53    inference(ennf_transformation,[],[f16])).
% 1.35/0.53  fof(f16,axiom,(
% 1.35/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.35/0.53  fof(f46,plain,(
% 1.35/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.35/0.53    inference(cnf_transformation,[],[f23])).
% 1.35/0.53  fof(f23,plain,(
% 1.35/0.53    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 1.35/0.53    inference(flattening,[],[f22])).
% 1.35/0.53  fof(f22,plain,(
% 1.35/0.53    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 1.35/0.53    inference(ennf_transformation,[],[f21])).
% 1.35/0.53  fof(f21,negated_conjecture,(
% 1.35/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 1.35/0.53    inference(negated_conjecture,[],[f20])).
% 1.35/0.53  fof(f20,conjecture,(
% 1.35/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).
% 1.35/0.53  fof(f113,plain,(
% 1.35/0.53    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) | spl3_2),
% 1.35/0.53    inference(avatar_component_clause,[],[f111])).
% 1.35/0.53  fof(f111,plain,(
% 1.35/0.53    spl3_2 <=> sK1 = k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))),
% 1.35/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.35/0.53  fof(f94,plain,(
% 1.35/0.53    v1_relat_1(sK2)),
% 1.35/0.53    inference(unit_resulting_resolution,[],[f54,f46,f53])).
% 1.35/0.53  fof(f53,plain,(
% 1.35/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.35/0.53    inference(cnf_transformation,[],[f26])).
% 1.35/0.53  fof(f26,plain,(
% 1.35/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.35/0.53    inference(ennf_transformation,[],[f5])).
% 1.35/0.53  fof(f5,axiom,(
% 1.35/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.35/0.53  fof(f54,plain,(
% 1.35/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.35/0.53    inference(cnf_transformation,[],[f6])).
% 1.35/0.53  fof(f6,axiom,(
% 1.35/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.35/0.53  fof(f89,plain,(
% 1.35/0.53    v2_funct_1(sK2)),
% 1.35/0.53    inference(unit_resulting_resolution,[],[f43,f45,f46,f55])).
% 1.35/0.53  fof(f55,plain,(
% 1.35/0.53    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.35/0.53    inference(cnf_transformation,[],[f28])).
% 1.35/0.53  fof(f28,plain,(
% 1.35/0.53    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.53    inference(flattening,[],[f27])).
% 1.35/0.53  fof(f27,plain,(
% 1.35/0.53    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.53    inference(ennf_transformation,[],[f17])).
% 1.35/0.53  fof(f17,axiom,(
% 1.35/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.35/0.53  fof(f45,plain,(
% 1.35/0.53    v3_funct_2(sK2,sK0,sK0)),
% 1.35/0.53    inference(cnf_transformation,[],[f23])).
% 1.35/0.53  fof(f43,plain,(
% 1.35/0.53    v1_funct_1(sK2)),
% 1.35/0.53    inference(cnf_transformation,[],[f23])).
% 1.35/0.53  fof(f47,plain,(
% 1.35/0.53    r1_tarski(sK1,sK0)),
% 1.35/0.53    inference(cnf_transformation,[],[f23])).
% 1.35/0.53  fof(f228,plain,(
% 1.35/0.53    spl3_2 | ~spl3_6),
% 1.35/0.53    inference(avatar_contradiction_clause,[],[f225])).
% 1.35/0.53  fof(f225,plain,(
% 1.35/0.53    $false | (spl3_2 | ~spl3_6)),
% 1.35/0.53    inference(unit_resulting_resolution,[],[f69,f202])).
% 1.35/0.53  fof(f202,plain,(
% 1.35/0.53    ~r1_tarski(k1_xboole_0,k1_relat_1(sK2)) | (spl3_2 | ~spl3_6)),
% 1.35/0.53    inference(backward_demodulation,[],[f151,f198])).
% 1.35/0.53  fof(f198,plain,(
% 1.35/0.53    k1_xboole_0 = sK1 | ~spl3_6),
% 1.35/0.53    inference(unit_resulting_resolution,[],[f69,f178,f50])).
% 1.35/0.53  fof(f50,plain,(
% 1.35/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.35/0.53    inference(cnf_transformation,[],[f2])).
% 1.35/0.53  fof(f2,axiom,(
% 1.35/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.35/0.53  fof(f178,plain,(
% 1.35/0.53    r1_tarski(sK1,k1_xboole_0) | ~spl3_6),
% 1.35/0.53    inference(backward_demodulation,[],[f47,f165])).
% 1.35/0.53  fof(f165,plain,(
% 1.35/0.53    k1_xboole_0 = sK0 | ~spl3_6),
% 1.35/0.53    inference(avatar_component_clause,[],[f163])).
% 1.35/0.53  fof(f163,plain,(
% 1.35/0.53    spl3_6 <=> k1_xboole_0 = sK0),
% 1.35/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.35/0.53  fof(f69,plain,(
% 1.35/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.35/0.53    inference(cnf_transformation,[],[f4])).
% 1.35/0.53  fof(f4,axiom,(
% 1.35/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.35/0.53  fof(f174,plain,(
% 1.35/0.53    spl3_5),
% 1.35/0.53    inference(avatar_contradiction_clause,[],[f171])).
% 1.35/0.53  fof(f171,plain,(
% 1.35/0.53    $false | spl3_5),
% 1.35/0.53    inference(unit_resulting_resolution,[],[f44,f161])).
% 1.35/0.53  fof(f161,plain,(
% 1.35/0.53    ~v1_funct_2(sK2,sK0,sK0) | spl3_5),
% 1.35/0.53    inference(avatar_component_clause,[],[f159])).
% 1.35/0.53  fof(f159,plain,(
% 1.35/0.53    spl3_5 <=> v1_funct_2(sK2,sK0,sK0)),
% 1.35/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.35/0.53  fof(f44,plain,(
% 1.35/0.53    v1_funct_2(sK2,sK0,sK0)),
% 1.35/0.53    inference(cnf_transformation,[],[f23])).
% 1.35/0.53  fof(f170,plain,(
% 1.35/0.53    ~spl3_5 | spl3_6 | spl3_7),
% 1.35/0.53    inference(avatar_split_clause,[],[f105,f167,f163,f159])).
% 1.35/0.53  fof(f105,plain,(
% 1.35/0.53    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK0 | ~v1_funct_2(sK2,sK0,sK0)),
% 1.35/0.53    inference(forward_demodulation,[],[f98,f91])).
% 1.35/0.53  fof(f91,plain,(
% 1.35/0.53    k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2)),
% 1.35/0.53    inference(unit_resulting_resolution,[],[f46,f68])).
% 1.35/0.53  fof(f68,plain,(
% 1.35/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.35/0.53    inference(cnf_transformation,[],[f38])).
% 1.35/0.53  fof(f38,plain,(
% 1.35/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.53    inference(ennf_transformation,[],[f14])).
% 1.35/0.53  fof(f14,axiom,(
% 1.35/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.35/0.53  fof(f98,plain,(
% 1.35/0.53    k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_2(sK2,sK0,sK0)),
% 1.35/0.53    inference(resolution,[],[f46,f62])).
% 1.35/0.53  fof(f62,plain,(
% 1.35/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.35/0.53    inference(cnf_transformation,[],[f30])).
% 1.35/0.53  fof(f30,plain,(
% 1.35/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.53    inference(flattening,[],[f29])).
% 1.35/0.53  fof(f29,plain,(
% 1.35/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.53    inference(ennf_transformation,[],[f18])).
% 1.35/0.53  fof(f18,axiom,(
% 1.35/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.35/0.53  fof(f140,plain,(
% 1.35/0.53    spl3_1),
% 1.35/0.53    inference(avatar_contradiction_clause,[],[f137])).
% 1.35/0.53  fof(f137,plain,(
% 1.35/0.53    $false | spl3_1),
% 1.35/0.53    inference(unit_resulting_resolution,[],[f47,f136])).
% 1.35/0.53  fof(f136,plain,(
% 1.35/0.53    ~r1_tarski(sK1,sK0) | spl3_1),
% 1.35/0.53    inference(forward_demodulation,[],[f135,f127])).
% 1.35/0.53  fof(f127,plain,(
% 1.35/0.53    sK0 = k2_relat_1(sK2)),
% 1.35/0.53    inference(unit_resulting_resolution,[],[f94,f90,f93,f67])).
% 1.35/0.53  fof(f67,plain,(
% 1.35/0.53    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 1.35/0.53    inference(cnf_transformation,[],[f37])).
% 1.35/0.53  fof(f37,plain,(
% 1.35/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.35/0.53    inference(flattening,[],[f36])).
% 1.35/0.53  fof(f36,plain,(
% 1.35/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.35/0.53    inference(ennf_transformation,[],[f19])).
% 1.35/0.53  fof(f19,axiom,(
% 1.35/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.35/0.53  fof(f93,plain,(
% 1.35/0.53    v5_relat_1(sK2,sK0)),
% 1.35/0.53    inference(unit_resulting_resolution,[],[f46,f72])).
% 1.35/0.53  fof(f72,plain,(
% 1.35/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.35/0.53    inference(cnf_transformation,[],[f40])).
% 1.35/0.53  fof(f40,plain,(
% 1.35/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.53    inference(ennf_transformation,[],[f13])).
% 1.35/0.53  fof(f13,axiom,(
% 1.35/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.35/0.53  fof(f90,plain,(
% 1.35/0.53    v2_funct_2(sK2,sK0)),
% 1.35/0.53    inference(unit_resulting_resolution,[],[f43,f45,f46,f56])).
% 1.35/0.53  fof(f56,plain,(
% 1.35/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1)) )),
% 1.35/0.53    inference(cnf_transformation,[],[f28])).
% 1.35/0.53  fof(f135,plain,(
% 1.35/0.53    ~r1_tarski(sK1,k2_relat_1(sK2)) | spl3_1),
% 1.35/0.53    inference(unit_resulting_resolution,[],[f43,f94,f109,f63])).
% 1.35/0.53  fof(f63,plain,(
% 1.35/0.53    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 1.35/0.53    inference(cnf_transformation,[],[f32])).
% 1.35/0.53  fof(f32,plain,(
% 1.35/0.53    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.35/0.53    inference(flattening,[],[f31])).
% 1.35/0.53  fof(f31,plain,(
% 1.35/0.53    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.35/0.53    inference(ennf_transformation,[],[f10])).
% 1.35/0.53  fof(f10,axiom,(
% 1.35/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 1.35/0.53  fof(f109,plain,(
% 1.35/0.53    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | spl3_1),
% 1.35/0.53    inference(avatar_component_clause,[],[f107])).
% 1.35/0.53  fof(f107,plain,(
% 1.35/0.53    spl3_1 <=> sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 1.35/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.35/0.53  fof(f114,plain,(
% 1.35/0.53    ~spl3_1 | ~spl3_2),
% 1.35/0.53    inference(avatar_split_clause,[],[f104,f111,f107])).
% 1.35/0.53  fof(f104,plain,(
% 1.35/0.53    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) | sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 1.35/0.53    inference(forward_demodulation,[],[f103,f87])).
% 1.35/0.53  fof(f87,plain,(
% 1.35/0.53    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK0,sK2,X0)) )),
% 1.35/0.53    inference(unit_resulting_resolution,[],[f46,f51])).
% 1.35/0.53  fof(f51,plain,(
% 1.35/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.35/0.53    inference(cnf_transformation,[],[f24])).
% 1.35/0.53  fof(f24,plain,(
% 1.35/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.53    inference(ennf_transformation,[],[f15])).
% 1.35/0.53  fof(f15,axiom,(
% 1.35/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.35/0.53  fof(f103,plain,(
% 1.35/0.53    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))),
% 1.35/0.53    inference(backward_demodulation,[],[f102,f87])).
% 1.35/0.53  fof(f102,plain,(
% 1.35/0.53    sK1 != k7_relset_1(sK0,sK0,sK2,k10_relat_1(sK2,sK1)) | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))),
% 1.35/0.53    inference(backward_demodulation,[],[f42,f88])).
% 1.35/0.53  fof(f42,plain,(
% 1.35/0.53    sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))),
% 1.35/0.53    inference(cnf_transformation,[],[f23])).
% 1.35/0.53  % SZS output end Proof for theBenchmark
% 1.35/0.53  % (21050)------------------------------
% 1.35/0.53  % (21050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (21050)Termination reason: Refutation
% 1.35/0.53  
% 1.35/0.53  % (21050)Memory used [KB]: 6268
% 1.35/0.53  % (21050)Time elapsed: 0.132 s
% 1.35/0.53  % (21050)------------------------------
% 1.35/0.53  % (21050)------------------------------
% 1.35/0.53  % (21045)Success in time 0.181 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:57:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 274 expanded)
%              Number of leaves         :   36 ( 115 expanded)
%              Depth                    :    9
%              Number of atoms          :  369 ( 631 expanded)
%              Number of equality atoms :   84 ( 139 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f326,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f72,f88,f94,f108,f114,f120,f137,f159,f164,f172,f215,f224,f234,f243,f263,f280,f286,f301,f310,f323])).

fof(f323,plain,
    ( ~ spl3_8
    | ~ spl3_1
    | spl3_3
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f322,f161,f69,f60,f117])).

fof(f117,plain,
    ( spl3_8
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f60,plain,
    ( spl3_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f69,plain,
    ( spl3_3
  <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f161,plain,
    ( spl3_14
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f322,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | ~ spl3_1
    | spl3_3
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f321,f163])).

fof(f163,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f321,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0)
    | ~ spl3_1
    | spl3_3 ),
    inference(forward_demodulation,[],[f71,f127])).

fof(f127,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0)
    | ~ spl3_1 ),
    inference(resolution,[],[f54,f62])).

fof(f62,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f71,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f310,plain,
    ( ~ spl3_13
    | spl3_27 ),
    inference(avatar_split_clause,[],[f308,f297,f155])).

fof(f155,plain,
    ( spl3_13
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f297,plain,
    ( spl3_27
  <=> r1_tarski(k10_relat_1(sK2,sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f308,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_27 ),
    inference(resolution,[],[f299,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f299,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),k1_relat_1(sK2))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f297])).

fof(f301,plain,
    ( spl3_17
    | ~ spl3_27
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f289,f277,f297,f212])).

fof(f212,plain,
    ( spl3_17
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f277,plain,
    ( spl3_25
  <=> r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f289,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),k1_relat_1(sK2))
    | k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ spl3_25 ),
    inference(resolution,[],[f279,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f279,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK1))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f277])).

fof(f286,plain,(
    spl3_24 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | spl3_24 ),
    inference(unit_resulting_resolution,[],[f57,f275])).

fof(f275,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl3_24
  <=> r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f280,plain,
    ( ~ spl3_13
    | ~ spl3_24
    | spl3_25
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f271,f260,f231,f277,f273,f155])).

fof(f231,plain,
    ( spl3_19
  <=> k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f260,plain,
    ( spl3_23
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f271,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK1))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f268,f233])).

fof(f233,plain,
    ( k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f231])).

fof(f268,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2)))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_23 ),
    inference(superposition,[],[f41,f262])).

fof(f262,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f260])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f263,plain,
    ( spl3_23
    | ~ spl3_1
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f248,f240,f60,f260])).

fof(f240,plain,
    ( spl3_20
  <=> sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f248,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_20 ),
    inference(superposition,[],[f122,f242])).

fof(f242,plain,
    ( sK2 = k7_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f240])).

fof(f122,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | ~ spl3_1 ),
    inference(resolution,[],[f95,f62])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ) ),
    inference(resolution,[],[f39,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f243,plain,
    ( spl3_20
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f237,f60,f240])).

fof(f237,plain,
    ( sK2 = k7_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f228,f57])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | sK2 = k7_relat_1(sK2,X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f225,f130])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | sK2 = k7_relat_1(sK2,X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f96,f62])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k7_relat_1(X0,X1) = X0
      | ~ v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f45,f49])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f225,plain,
    ( ! [X0] :
        ( v4_relat_1(sK2,X0)
        | ~ r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f202,f62])).

fof(f202,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ r1_tarski(k1_relat_1(X8),X9)
      | v4_relat_1(X8,X9) ) ),
    inference(resolution,[],[f56,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f234,plain,
    ( spl3_19
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f229,f221,f155,f231])).

fof(f221,plain,
    ( spl3_18
  <=> k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f229,plain,
    ( k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(superposition,[],[f176,f223])).

fof(f223,plain,
    ( k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f221])).

fof(f176,plain,
    ( ! [X3] : k10_relat_1(sK2,X3) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X3))
    | ~ spl3_13 ),
    inference(resolution,[],[f156,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f156,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f155])).

fof(f224,plain,
    ( spl3_18
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f218,f161,f151,f91,f221])).

fof(f91,plain,
    ( spl3_5
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f151,plain,
    ( spl3_12
  <=> ! [X5] :
        ( k9_relat_1(sK2,sK0) = k3_xboole_0(k9_relat_1(sK2,sK0),X5)
        | ~ v5_relat_1(sK2,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f218,plain,
    ( k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1)
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(resolution,[],[f167,f93])).

fof(f93,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f167,plain,
    ( ! [X5] :
        ( ~ v5_relat_1(sK2,X5)
        | k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),X5) )
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f152,f163])).

fof(f152,plain,
    ( ! [X5] :
        ( k9_relat_1(sK2,sK0) = k3_xboole_0(k9_relat_1(sK2,sK0),X5)
        | ~ v5_relat_1(sK2,X5) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f151])).

fof(f215,plain,
    ( ~ spl3_17
    | ~ spl3_1
    | spl3_7 ),
    inference(avatar_split_clause,[],[f210,f111,f60,f212])).

fof(f111,plain,
    ( spl3_7
  <=> k8_relset_1(sK0,sK1,sK2,sK1) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f210,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,sK1)
    | ~ spl3_1
    | spl3_7 ),
    inference(superposition,[],[f113,f131])).

fof(f131,plain,
    ( ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl3_1 ),
    inference(resolution,[],[f55,f62])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f113,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f172,plain,
    ( ~ spl3_1
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl3_1
    | spl3_13 ),
    inference(subsumption_resolution,[],[f62,f170])).

fof(f170,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_13 ),
    inference(resolution,[],[f157,f49])).

fof(f157,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f155])).

fof(f164,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f142,f134,f60,f161])).

fof(f134,plain,
    ( spl3_9
  <=> sK2 = k7_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f142,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(superposition,[],[f122,f136])).

fof(f136,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f159,plain,
    ( spl3_12
    | ~ spl3_13
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f141,f134,f60,f155,f151])).

fof(f141,plain,
    ( ! [X7] :
        ( ~ v1_relat_1(sK2)
        | ~ v5_relat_1(sK2,X7)
        | k9_relat_1(sK2,sK0) = k3_xboole_0(k9_relat_1(sK2,sK0),X7) )
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(superposition,[],[f126,f136])).

fof(f126,plain,
    ( ! [X4,X5] :
        ( ~ v1_relat_1(k7_relat_1(sK2,X4))
        | ~ v5_relat_1(k7_relat_1(sK2,X4),X5)
        | k9_relat_1(sK2,X4) = k3_xboole_0(k9_relat_1(sK2,X4),X5) )
    | ~ spl3_1 ),
    inference(resolution,[],[f123,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f123,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(sK2,X0),X1)
        | ~ v1_relat_1(k7_relat_1(sK2,X0))
        | ~ v5_relat_1(k7_relat_1(sK2,X0),X1) )
    | ~ spl3_1 ),
    inference(superposition,[],[f43,f122])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f137,plain,
    ( spl3_9
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f132,f85,f60,f134])).

fof(f85,plain,
    ( spl3_4
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f132,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(resolution,[],[f130,f87])).

fof(f87,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f120,plain,
    ( spl3_8
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f115,f60,f117])).

fof(f115,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f51,f62])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f114,plain,
    ( ~ spl3_7
    | spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f109,f105,f65,f111])).

fof(f65,plain,
    ( spl3_2
  <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f105,plain,
    ( spl3_6
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f109,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | spl3_2
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f67,f107])).

fof(f107,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f67,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f108,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f103,f60,f105])).

fof(f103,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f50,f62])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f94,plain,
    ( spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f89,f60,f91])).

fof(f89,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f53,f62])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f83,f60,f85])).

fof(f83,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f52,f62])).

fof(f72,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f36,f69,f65])).

fof(f36,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f63,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f37,f60])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:38:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (10891)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.46  % (10899)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.47  % (10899)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f326,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f63,f72,f88,f94,f108,f114,f120,f137,f159,f164,f172,f215,f224,f234,f243,f263,f280,f286,f301,f310,f323])).
% 0.21/0.47  fof(f323,plain,(
% 0.21/0.47    ~spl3_8 | ~spl3_1 | spl3_3 | ~spl3_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f322,f161,f69,f60,f117])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    spl3_8 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl3_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl3_3 <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    spl3_14 <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.47  fof(f322,plain,(
% 0.21/0.47    k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2) | (~spl3_1 | spl3_3 | ~spl3_14)),
% 0.21/0.47    inference(forward_demodulation,[],[f321,f163])).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | ~spl3_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f161])).
% 0.21/0.47  fof(f321,plain,(
% 0.21/0.47    k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0) | (~spl3_1 | spl3_3)),
% 0.21/0.47    inference(forward_demodulation,[],[f71,f127])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0)) ) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f54,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f60])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) | spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f69])).
% 0.21/0.47  fof(f310,plain,(
% 0.21/0.47    ~spl3_13 | spl3_27),
% 0.21/0.47    inference(avatar_split_clause,[],[f308,f297,f155])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    spl3_13 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.47  fof(f297,plain,(
% 0.21/0.47    spl3_27 <=> r1_tarski(k10_relat_1(sK2,sK1),k1_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.47  fof(f308,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | spl3_27),
% 0.21/0.47    inference(resolution,[],[f299,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.47  fof(f299,plain,(
% 0.21/0.47    ~r1_tarski(k10_relat_1(sK2,sK1),k1_relat_1(sK2)) | spl3_27),
% 0.21/0.47    inference(avatar_component_clause,[],[f297])).
% 0.21/0.47  fof(f301,plain,(
% 0.21/0.47    spl3_17 | ~spl3_27 | ~spl3_25),
% 0.21/0.47    inference(avatar_split_clause,[],[f289,f277,f297,f212])).
% 0.21/0.47  fof(f212,plain,(
% 0.21/0.47    spl3_17 <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.47  fof(f277,plain,(
% 0.21/0.47    spl3_25 <=> r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.47  fof(f289,plain,(
% 0.21/0.47    ~r1_tarski(k10_relat_1(sK2,sK1),k1_relat_1(sK2)) | k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | ~spl3_25),
% 0.21/0.47    inference(resolution,[],[f279,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.47  fof(f279,plain,(
% 0.21/0.47    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK1)) | ~spl3_25),
% 0.21/0.47    inference(avatar_component_clause,[],[f277])).
% 0.21/0.47  fof(f286,plain,(
% 0.21/0.47    spl3_24),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f283])).
% 0.21/0.47  fof(f283,plain,(
% 0.21/0.47    $false | spl3_24),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f57,f275])).
% 0.21/0.47  fof(f275,plain,(
% 0.21/0.47    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) | spl3_24),
% 0.21/0.47    inference(avatar_component_clause,[],[f273])).
% 0.21/0.47  fof(f273,plain,(
% 0.21/0.47    spl3_24 <=> r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f280,plain,(
% 0.21/0.47    ~spl3_13 | ~spl3_24 | spl3_25 | ~spl3_19 | ~spl3_23),
% 0.21/0.47    inference(avatar_split_clause,[],[f271,f260,f231,f277,f273,f155])).
% 0.21/0.47  fof(f231,plain,(
% 0.21/0.47    spl3_19 <=> k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.47  fof(f260,plain,(
% 0.21/0.47    spl3_23 <=> k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.47  fof(f271,plain,(
% 0.21/0.47    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK1)) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_19 | ~spl3_23)),
% 0.21/0.47    inference(forward_demodulation,[],[f268,f233])).
% 0.21/0.47  fof(f233,plain,(
% 0.21/0.47    k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl3_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f231])).
% 0.21/0.47  fof(f268,plain,(
% 0.21/0.47    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl3_23),
% 0.21/0.47    inference(superposition,[],[f41,f262])).
% 0.21/0.47  fof(f262,plain,(
% 0.21/0.47    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) | ~spl3_23),
% 0.21/0.47    inference(avatar_component_clause,[],[f260])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 0.21/0.47  fof(f263,plain,(
% 0.21/0.47    spl3_23 | ~spl3_1 | ~spl3_20),
% 0.21/0.47    inference(avatar_split_clause,[],[f248,f240,f60,f260])).
% 0.21/0.47  fof(f240,plain,(
% 0.21/0.47    spl3_20 <=> sK2 = k7_relat_1(sK2,k1_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.47  fof(f248,plain,(
% 0.21/0.47    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) | (~spl3_1 | ~spl3_20)),
% 0.21/0.47    inference(superposition,[],[f122,f242])).
% 0.21/0.47  fof(f242,plain,(
% 0.21/0.47    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) | ~spl3_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f240])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) ) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f95,f62])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)) )),
% 0.21/0.47    inference(resolution,[],[f39,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.47  fof(f243,plain,(
% 0.21/0.47    spl3_20 | ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f237,f60,f240])).
% 0.21/0.47  fof(f237,plain,(
% 0.21/0.47    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f228,f57])).
% 0.21/0.47  fof(f228,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | sK2 = k7_relat_1(sK2,X0)) ) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f225,f130])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    ( ! [X0] : (~v4_relat_1(sK2,X0) | sK2 = k7_relat_1(sK2,X0)) ) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f96,f62])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k7_relat_1(X0,X1) = X0 | ~v4_relat_1(X0,X1)) )),
% 0.21/0.47    inference(resolution,[],[f45,f49])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.47  fof(f225,plain,(
% 0.21/0.47    ( ! [X0] : (v4_relat_1(sK2,X0) | ~r1_tarski(k1_relat_1(sK2),X0)) ) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f202,f62])).
% 0.21/0.47  fof(f202,plain,(
% 0.21/0.47    ( ! [X10,X8,X11,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~r1_tarski(k1_relat_1(X8),X9) | v4_relat_1(X8,X9)) )),
% 0.21/0.47    inference(resolution,[],[f56,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.47    inference(flattening,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.47    inference(ennf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.21/0.47  fof(f234,plain,(
% 0.21/0.47    spl3_19 | ~spl3_13 | ~spl3_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f229,f221,f155,f231])).
% 0.21/0.47  fof(f221,plain,(
% 0.21/0.47    spl3_18 <=> k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.47  fof(f229,plain,(
% 0.21/0.47    k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2)) | (~spl3_13 | ~spl3_18)),
% 0.21/0.47    inference(superposition,[],[f176,f223])).
% 0.21/0.47  fof(f223,plain,(
% 0.21/0.47    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1) | ~spl3_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f221])).
% 0.21/0.47  fof(f176,plain,(
% 0.21/0.47    ( ! [X3] : (k10_relat_1(sK2,X3) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X3))) ) | ~spl3_13),
% 0.21/0.47    inference(resolution,[],[f156,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    v1_relat_1(sK2) | ~spl3_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f155])).
% 0.21/0.47  fof(f224,plain,(
% 0.21/0.47    spl3_18 | ~spl3_5 | ~spl3_12 | ~spl3_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f218,f161,f151,f91,f221])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    spl3_5 <=> v5_relat_1(sK2,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    spl3_12 <=> ! [X5] : (k9_relat_1(sK2,sK0) = k3_xboole_0(k9_relat_1(sK2,sK0),X5) | ~v5_relat_1(sK2,X5))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.47  fof(f218,plain,(
% 0.21/0.47    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1) | (~spl3_5 | ~spl3_12 | ~spl3_14)),
% 0.21/0.47    inference(resolution,[],[f167,f93])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    v5_relat_1(sK2,sK1) | ~spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f91])).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    ( ! [X5] : (~v5_relat_1(sK2,X5) | k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),X5)) ) | (~spl3_12 | ~spl3_14)),
% 0.21/0.47    inference(forward_demodulation,[],[f152,f163])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    ( ! [X5] : (k9_relat_1(sK2,sK0) = k3_xboole_0(k9_relat_1(sK2,sK0),X5) | ~v5_relat_1(sK2,X5)) ) | ~spl3_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f151])).
% 0.21/0.47  fof(f215,plain,(
% 0.21/0.47    ~spl3_17 | ~spl3_1 | spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f210,f111,f60,f212])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    spl3_7 <=> k8_relset_1(sK0,sK1,sK2,sK1) = k1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f210,plain,(
% 0.21/0.47    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) | (~spl3_1 | spl3_7)),
% 0.21/0.47    inference(superposition,[],[f113,f131])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ( ! [X0] : (k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)) ) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f55,f62])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) | spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f111])).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    ~spl3_1 | spl3_13),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.47  fof(f171,plain,(
% 0.21/0.47    $false | (~spl3_1 | spl3_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f62,f170])).
% 0.21/0.47  fof(f170,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_13),
% 0.21/0.47    inference(resolution,[],[f157,f49])).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | spl3_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f155])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    spl3_14 | ~spl3_1 | ~spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f142,f134,f60,f161])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    spl3_9 <=> sK2 = k7_relat_1(sK2,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | (~spl3_1 | ~spl3_9)),
% 0.21/0.47    inference(superposition,[],[f122,f136])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    sK2 = k7_relat_1(sK2,sK0) | ~spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f134])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    spl3_12 | ~spl3_13 | ~spl3_1 | ~spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f141,f134,f60,f155,f151])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ( ! [X7] : (~v1_relat_1(sK2) | ~v5_relat_1(sK2,X7) | k9_relat_1(sK2,sK0) = k3_xboole_0(k9_relat_1(sK2,sK0),X7)) ) | (~spl3_1 | ~spl3_9)),
% 0.21/0.47    inference(superposition,[],[f126,f136])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    ( ! [X4,X5] : (~v1_relat_1(k7_relat_1(sK2,X4)) | ~v5_relat_1(k7_relat_1(sK2,X4),X5) | k9_relat_1(sK2,X4) = k3_xboole_0(k9_relat_1(sK2,X4),X5)) ) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f123,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),X1) | ~v1_relat_1(k7_relat_1(sK2,X0)) | ~v5_relat_1(k7_relat_1(sK2,X0),X1)) ) | ~spl3_1),
% 0.21/0.47    inference(superposition,[],[f43,f122])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    spl3_9 | ~spl3_1 | ~spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f132,f85,f60,f134])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    spl3_4 <=> v4_relat_1(sK2,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    sK2 = k7_relat_1(sK2,sK0) | (~spl3_1 | ~spl3_4)),
% 0.21/0.47    inference(resolution,[],[f130,f87])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    v4_relat_1(sK2,sK0) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f85])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    spl3_8 | ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f115,f60,f117])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f51,f62])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    ~spl3_7 | spl3_2 | ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f109,f105,f65,f111])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl3_2 <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    spl3_6 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) | (spl3_2 | ~spl3_6)),
% 0.21/0.47    inference(backward_demodulation,[],[f67,f107])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl3_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f105])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f65])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    spl3_6 | ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f103,f60,f105])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f50,f62])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl3_5 | ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f89,f60,f91])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    v5_relat_1(sK2,sK1) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f53,f62])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl3_4 | ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f83,f60,f85])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    v4_relat_1(sK2,sK0) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f52,f62])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ~spl3_2 | ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f36,f69,f65])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.21/0.47    inference(negated_conjecture,[],[f16])).
% 0.21/0.47  fof(f16,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f37,f60])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (10899)------------------------------
% 0.21/0.47  % (10899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (10899)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (10899)Memory used [KB]: 6396
% 0.21/0.47  % (10899)Time elapsed: 0.056 s
% 0.21/0.47  % (10899)------------------------------
% 0.21/0.47  % (10899)------------------------------
% 0.21/0.47  % (10883)Success in time 0.118 s
%------------------------------------------------------------------------------

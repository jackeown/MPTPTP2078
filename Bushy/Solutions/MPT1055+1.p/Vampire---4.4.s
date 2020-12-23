%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t172_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:36 EDT 2019

% Result     : Theorem 0.91s
% Output     : Refutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :  452 (1334 expanded)
%              Number of leaves         :  108 ( 518 expanded)
%              Depth                    :   12
%              Number of atoms          : 1283 (3497 expanded)
%              Number of equality atoms :   41 ( 215 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4191,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f103,f110,f117,f124,f131,f138,f145,f158,f159,f168,f176,f188,f201,f222,f245,f260,f268,f282,f309,f321,f477,f505,f519,f538,f566,f580,f590,f592,f602,f604,f613,f630,f633,f671,f679,f690,f816,f852,f856,f857,f858,f879,f898,f1219,f1446,f1687,f1722,f1937,f2035,f2301,f2357,f2364,f2460,f2549,f2559,f2571,f2586,f2589,f2680,f2774,f2792,f2879,f3100,f3110,f3135,f3139,f3148,f3163,f3171,f3178,f3185,f3194,f3286,f3319,f3427,f3453,f3564,f3603,f3618,f3619,f3671,f3727,f3734,f3795,f3859,f3886,f3960,f4059,f4061,f4169])).

fof(f4169,plain,
    ( ~ spl6_24
    | ~ spl6_26
    | spl6_31
    | ~ spl6_32
    | ~ spl6_70 ),
    inference(avatar_contradiction_clause,[],[f4168])).

fof(f4168,plain,
    ( $false
    | ~ spl6_24
    | ~ spl6_26
    | ~ spl6_31
    | ~ spl6_32
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f4167,f241])).

fof(f241,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl6_31
  <=> ~ r1_tarski(sK3,k10_relat_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f4167,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_24
    | ~ spl6_26
    | ~ spl6_32
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f4141,f187])).

fof(f187,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl6_24
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f4141,plain,
    ( ~ r1_tarski(sK3,sK0)
    | r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_26
    | ~ spl6_32
    | ~ spl6_70 ),
    inference(resolution,[],[f675,f256])).

fof(f256,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl6_32
  <=> r1_tarski(k9_relat_1(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f675,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,k10_relat_1(sK2,X1)) )
    | ~ spl6_26
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f672,f200])).

fof(f200,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl6_26
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f672,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK0)
        | ~ v1_relat_1(sK2)
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | r1_tarski(X0,k10_relat_1(sK2,X1)) )
    | ~ spl6_70 ),
    inference(resolution,[],[f670,f214])).

fof(f214,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X3,k10_relat_1(X2,X1)) ) ),
    inference(resolution,[],[f72,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t172_funct_2.p',t1_xboole_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t172_funct_2.p',t178_relat_1)).

fof(f670,plain,
    ( ! [X1] :
        ( r1_tarski(X1,k10_relat_1(sK2,k9_relat_1(sK2,X1)))
        | ~ r1_tarski(X1,sK0) )
    | ~ spl6_70 ),
    inference(avatar_component_clause,[],[f669])).

fof(f669,plain,
    ( spl6_70
  <=> ! [X1] :
        ( r1_tarski(X1,k10_relat_1(sK2,k9_relat_1(sK2,X1)))
        | ~ r1_tarski(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f4061,plain,(
    ~ spl6_146 ),
    inference(avatar_contradiction_clause,[],[f4060])).

fof(f4060,plain,
    ( $false
    | ~ spl6_146 ),
    inference(resolution,[],[f4058,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t172_funct_2.p',existence_m1_subset_1)).

fof(f4058,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k9_relat_1(sK2,sK3))
    | ~ spl6_146 ),
    inference(avatar_component_clause,[],[f4057])).

fof(f4057,plain,
    ( spl6_146
  <=> ! [X2] : ~ m1_subset_1(X2,k9_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_146])])).

fof(f4059,plain,
    ( spl6_146
    | spl6_102
    | ~ spl6_20
    | ~ spl6_128 ),
    inference(avatar_split_clause,[],[f3892,f3176,f166,f2352,f4057])).

fof(f2352,plain,
    ( spl6_102
  <=> v1_xboole_0(k9_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).

fof(f166,plain,
    ( spl6_20
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f3176,plain,
    ( spl6_128
  <=> r1_tarski(k9_relat_1(sK2,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_128])])).

fof(f3892,plain,
    ( ! [X2] :
        ( v1_xboole_0(k9_relat_1(sK2,sK3))
        | ~ m1_subset_1(X2,k9_relat_1(sK2,sK3)) )
    | ~ spl6_20
    | ~ spl6_128 ),
    inference(subsumption_resolution,[],[f3188,f167])).

fof(f167,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f166])).

fof(f3188,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | v1_xboole_0(k9_relat_1(sK2,sK3))
        | ~ m1_subset_1(X2,k9_relat_1(sK2,sK3)) )
    | ~ spl6_128 ),
    inference(resolution,[],[f3177,f314])).

fof(f314,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,X1) ) ),
    inference(resolution,[],[f203,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t172_funct_2.p',t2_subset)).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f79,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t172_funct_2.p',t3_subset)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t172_funct_2.p',t5_subset)).

fof(f3177,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),k1_xboole_0)
    | ~ spl6_128 ),
    inference(avatar_component_clause,[],[f3176])).

fof(f3960,plain,
    ( spl6_144
    | ~ spl6_128 ),
    inference(avatar_split_clause,[],[f3937,f3176,f3958])).

fof(f3958,plain,
    ( spl6_144
  <=> r1_tarski(sK5(k1_zfmisc_1(k9_relat_1(sK2,sK3))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_144])])).

fof(f3937,plain,
    ( r1_tarski(sK5(k1_zfmisc_1(k9_relat_1(sK2,sK3))),k1_xboole_0)
    | ~ spl6_128 ),
    inference(resolution,[],[f3187,f181])).

fof(f181,plain,(
    ! [X2] : r1_tarski(sK5(k1_zfmisc_1(X2)),X2) ),
    inference(resolution,[],[f75,f84])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3187,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k9_relat_1(sK2,sK3))
        | r1_tarski(X1,k1_xboole_0) )
    | ~ spl6_128 ),
    inference(resolution,[],[f3177,f71])).

fof(f3886,plain,
    ( ~ spl6_26
    | spl6_31
    | ~ spl6_108
    | ~ spl6_126 ),
    inference(avatar_contradiction_clause,[],[f3885])).

fof(f3885,plain,
    ( $false
    | ~ spl6_26
    | ~ spl6_31
    | ~ spl6_108
    | ~ spl6_126 ),
    inference(subsumption_resolution,[],[f3874,f2459])).

fof(f2459,plain,
    ( r1_tarski(k1_xboole_0,sK4)
    | ~ spl6_108 ),
    inference(avatar_component_clause,[],[f2458])).

fof(f2458,plain,
    ( spl6_108
  <=> r1_tarski(k1_xboole_0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_108])])).

fof(f3874,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | ~ spl6_26
    | ~ spl6_31
    | ~ spl6_126 ),
    inference(resolution,[],[f3870,f241])).

fof(f3870,plain,
    ( ! [X0] :
        ( r1_tarski(sK3,k10_relat_1(sK2,X0))
        | ~ r1_tarski(k1_xboole_0,X0) )
    | ~ spl6_26
    | ~ spl6_126 ),
    inference(subsumption_resolution,[],[f3861,f200])).

fof(f3861,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ r1_tarski(k1_xboole_0,X0)
        | r1_tarski(sK3,k10_relat_1(sK2,X0)) )
    | ~ spl6_126 ),
    inference(resolution,[],[f3167,f214])).

fof(f3167,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,k1_xboole_0))
    | ~ spl6_126 ),
    inference(avatar_component_clause,[],[f3166])).

fof(f3166,plain,
    ( spl6_126
  <=> r1_tarski(sK3,k10_relat_1(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_126])])).

fof(f3859,plain,
    ( spl6_126
    | ~ spl6_24
    | ~ spl6_70
    | ~ spl6_142 ),
    inference(avatar_split_clause,[],[f3814,f3732,f669,f186,f3166])).

fof(f3732,plain,
    ( spl6_142
  <=> k1_xboole_0 = k9_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_142])])).

fof(f3814,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,k1_xboole_0))
    | ~ spl6_24
    | ~ spl6_70
    | ~ spl6_142 ),
    inference(subsumption_resolution,[],[f3771,f187])).

fof(f3771,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,k1_xboole_0))
    | ~ r1_tarski(sK3,sK0)
    | ~ spl6_70
    | ~ spl6_142 ),
    inference(superposition,[],[f670,f3733])).

fof(f3733,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,sK3)
    | ~ spl6_142 ),
    inference(avatar_component_clause,[],[f3732])).

fof(f3795,plain,
    ( ~ spl6_24
    | ~ spl6_70
    | spl6_127
    | ~ spl6_142 ),
    inference(avatar_contradiction_clause,[],[f3794])).

fof(f3794,plain,
    ( $false
    | ~ spl6_24
    | ~ spl6_70
    | ~ spl6_127
    | ~ spl6_142 ),
    inference(subsumption_resolution,[],[f3793,f187])).

fof(f3793,plain,
    ( ~ r1_tarski(sK3,sK0)
    | ~ spl6_70
    | ~ spl6_127
    | ~ spl6_142 ),
    inference(subsumption_resolution,[],[f3771,f3170])).

fof(f3170,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,k1_xboole_0))
    | ~ spl6_127 ),
    inference(avatar_component_clause,[],[f3169])).

fof(f3169,plain,
    ( spl6_127
  <=> ~ r1_tarski(sK3,k10_relat_1(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_127])])).

fof(f3734,plain,
    ( spl6_142
    | ~ spl6_102 ),
    inference(avatar_split_clause,[],[f3214,f2352,f3732])).

fof(f3214,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,sK3)
    | ~ spl6_102 ),
    inference(resolution,[],[f2353,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t172_funct_2.p',t6_boole)).

fof(f2353,plain,
    ( v1_xboole_0(k9_relat_1(sK2,sK3))
    | ~ spl6_102 ),
    inference(avatar_component_clause,[],[f2352])).

fof(f3727,plain,
    ( ~ spl6_53
    | spl6_138
    | spl6_140
    | ~ spl6_78
    | ~ spl6_102 ),
    inference(avatar_split_clause,[],[f3341,f2352,f877,f3725,f3722,f530])).

fof(f530,plain,
    ( spl6_53
  <=> ~ v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f3722,plain,
    ( spl6_138
  <=> v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_138])])).

fof(f3725,plain,
    ( spl6_140
  <=> ! [X1] : ~ m1_subset_1(X1,sK5(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_140])])).

fof(f877,plain,
    ( spl6_78
  <=> r1_tarski(sK5(k1_zfmisc_1(k9_relat_1(sK2,sK3))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f3341,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK5(k1_zfmisc_1(k1_xboole_0)))
        | v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0)))
        | ~ v1_xboole_0(sK4) )
    | ~ spl6_78
    | ~ spl6_102 ),
    inference(forward_demodulation,[],[f3340,f3214])).

fof(f3340,plain,
    ( ! [X1] :
        ( v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0)))
        | ~ v1_xboole_0(sK4)
        | ~ m1_subset_1(X1,sK5(k1_zfmisc_1(k9_relat_1(sK2,sK3)))) )
    | ~ spl6_78
    | ~ spl6_102 ),
    inference(forward_demodulation,[],[f2487,f3214])).

fof(f2487,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(sK4)
        | v1_xboole_0(sK5(k1_zfmisc_1(k9_relat_1(sK2,sK3))))
        | ~ m1_subset_1(X1,sK5(k1_zfmisc_1(k9_relat_1(sK2,sK3)))) )
    | ~ spl6_78 ),
    inference(resolution,[],[f878,f314])).

fof(f878,plain,
    ( r1_tarski(sK5(k1_zfmisc_1(k9_relat_1(sK2,sK3))),sK4)
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f877])).

fof(f3671,plain,
    ( ~ spl6_137
    | ~ spl6_102
    | spl6_121 ),
    inference(avatar_split_clause,[],[f3216,f2874,f2352,f3669])).

fof(f3669,plain,
    ( spl6_137
  <=> ~ m1_subset_1(sK5(k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_137])])).

fof(f2874,plain,
    ( spl6_121
  <=> ~ m1_subset_1(sK5(k9_relat_1(sK2,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).

fof(f3216,plain,
    ( ~ m1_subset_1(sK5(k1_xboole_0),sK1)
    | ~ spl6_102
    | ~ spl6_121 ),
    inference(backward_demodulation,[],[f3214,f2875])).

fof(f2875,plain,
    ( ~ m1_subset_1(sK5(k9_relat_1(sK2,sK3)),sK1)
    | ~ spl6_121 ),
    inference(avatar_component_clause,[],[f2874])).

fof(f3619,plain,
    ( spl6_52
    | spl6_54
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f796,f220,f536,f533])).

fof(f533,plain,
    ( spl6_52
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f536,plain,
    ( spl6_54
  <=> ! [X0] :
        ( m1_subset_1(X0,sK1)
        | ~ m1_subset_1(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f220,plain,
    ( spl6_28
  <=> r1_tarski(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f796,plain,
    ( ! [X70] :
        ( m1_subset_1(X70,sK1)
        | v1_xboole_0(sK4)
        | ~ m1_subset_1(X70,sK4) )
    | ~ spl6_28 ),
    inference(resolution,[],[f323,f221])).

fof(f221,plain,
    ( r1_tarski(sK4,sK1)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f220])).

fof(f323,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | m1_subset_1(X0,X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X2) ) ),
    inference(resolution,[],[f208,f82])).

fof(f208,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f80,f74])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t172_funct_2.p',t4_subset)).

fof(f3618,plain,
    ( ~ spl6_135
    | ~ spl6_102
    | spl6_111 ),
    inference(avatar_split_clause,[],[f3324,f2544,f2352,f3616])).

fof(f3616,plain,
    ( spl6_135
  <=> ~ m1_subset_1(sK5(k1_xboole_0),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_135])])).

fof(f2544,plain,
    ( spl6_111
  <=> ~ m1_subset_1(sK5(k9_relat_1(sK2,sK3)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).

fof(f3324,plain,
    ( ~ m1_subset_1(sK5(k1_xboole_0),sK4)
    | ~ spl6_102
    | ~ spl6_111 ),
    inference(forward_demodulation,[],[f2545,f3214])).

fof(f2545,plain,
    ( ~ m1_subset_1(sK5(k9_relat_1(sK2,sK3)),sK4)
    | ~ spl6_111 ),
    inference(avatar_component_clause,[],[f2544])).

fof(f3603,plain,
    ( spl6_132
    | ~ spl6_28
    | ~ spl6_112 ),
    inference(avatar_split_clause,[],[f3473,f2584,f220,f3601])).

fof(f3601,plain,
    ( spl6_132
  <=> r1_tarski(sK5(k1_zfmisc_1(k1_xboole_0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_132])])).

fof(f2584,plain,
    ( spl6_112
  <=> r1_tarski(sK5(k1_zfmisc_1(k1_xboole_0)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_112])])).

fof(f3473,plain,
    ( r1_tarski(sK5(k1_zfmisc_1(k1_xboole_0)),sK1)
    | ~ spl6_28
    | ~ spl6_112 ),
    inference(resolution,[],[f253,f2585])).

fof(f2585,plain,
    ( r1_tarski(sK5(k1_zfmisc_1(k1_xboole_0)),sK4)
    | ~ spl6_112 ),
    inference(avatar_component_clause,[],[f2584])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK4)
        | r1_tarski(X0,sK1) )
    | ~ spl6_28 ),
    inference(resolution,[],[f221,f71])).

fof(f3564,plain,
    ( ~ spl6_20
    | spl6_53
    | ~ spl6_96 ),
    inference(avatar_contradiction_clause,[],[f3563])).

fof(f3563,plain,
    ( $false
    | ~ spl6_20
    | ~ spl6_53
    | ~ spl6_96 ),
    inference(resolution,[],[f3486,f84])).

fof(f3486,plain,
    ( ! [X2] : ~ m1_subset_1(X2,sK4)
    | ~ spl6_20
    | ~ spl6_53
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f3485,f531])).

fof(f531,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f530])).

fof(f3485,plain,
    ( ! [X2] :
        ( v1_xboole_0(sK4)
        | ~ m1_subset_1(X2,sK4) )
    | ~ spl6_20
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f3479,f167])).

fof(f3479,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | v1_xboole_0(sK4)
        | ~ m1_subset_1(X2,sK4) )
    | ~ spl6_96 ),
    inference(resolution,[],[f2031,f314])).

fof(f2031,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ spl6_96 ),
    inference(avatar_component_clause,[],[f2030])).

fof(f2030,plain,
    ( spl6_96
  <=> r1_tarski(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f3453,plain,
    ( spl6_112
    | ~ spl6_78
    | ~ spl6_102 ),
    inference(avatar_split_clause,[],[f2376,f2352,f877,f2584])).

fof(f2376,plain,
    ( r1_tarski(sK5(k1_zfmisc_1(k1_xboole_0)),sK4)
    | ~ spl6_78
    | ~ spl6_102 ),
    inference(backward_demodulation,[],[f2366,f878])).

fof(f2366,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,sK3)
    | ~ spl6_102 ),
    inference(resolution,[],[f2353,f87])).

fof(f3427,plain,
    ( spl6_108
    | ~ spl6_32
    | ~ spl6_102 ),
    inference(avatar_split_clause,[],[f2367,f2352,f255,f2458])).

fof(f2367,plain,
    ( r1_tarski(k1_xboole_0,sK4)
    | ~ spl6_32
    | ~ spl6_102 ),
    inference(backward_demodulation,[],[f2366,f256])).

fof(f3319,plain,
    ( ~ spl6_52
    | ~ spl6_102
    | spl6_111 ),
    inference(avatar_contradiction_clause,[],[f3318])).

fof(f3318,plain,
    ( $false
    | ~ spl6_52
    | ~ spl6_102
    | ~ spl6_111 ),
    inference(subsumption_resolution,[],[f3282,f84])).

fof(f3282,plain,
    ( ~ m1_subset_1(sK5(k1_xboole_0),k1_xboole_0)
    | ~ spl6_52
    | ~ spl6_102
    | ~ spl6_111 ),
    inference(backward_demodulation,[],[f3214,f3132])).

fof(f3132,plain,
    ( ~ m1_subset_1(sK5(k9_relat_1(sK2,sK3)),k1_xboole_0)
    | ~ spl6_52
    | ~ spl6_111 ),
    inference(forward_demodulation,[],[f2545,f2882])).

fof(f2882,plain,
    ( k1_xboole_0 = sK4
    | ~ spl6_52 ),
    inference(resolution,[],[f534,f87])).

fof(f534,plain,
    ( v1_xboole_0(sK4)
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f533])).

fof(f3286,plain,
    ( ~ spl6_52
    | ~ spl6_66
    | ~ spl6_102
    | spl6_121 ),
    inference(avatar_contradiction_clause,[],[f3285])).

fof(f3285,plain,
    ( $false
    | ~ spl6_52
    | ~ spl6_66
    | ~ spl6_102
    | ~ spl6_121 ),
    inference(subsumption_resolution,[],[f3216,f2896])).

fof(f2896,plain,
    ( m1_subset_1(sK5(k1_xboole_0),sK1)
    | ~ spl6_52
    | ~ spl6_66 ),
    inference(backward_demodulation,[],[f2882,f629])).

fof(f629,plain,
    ( m1_subset_1(sK5(sK4),sK1)
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f628])).

fof(f628,plain,
    ( spl6_66
  <=> m1_subset_1(sK5(sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f3194,plain,
    ( ~ spl6_51
    | ~ spl6_52
    | spl6_87 ),
    inference(avatar_split_clause,[],[f2970,f1676,f533,f517])).

fof(f517,plain,
    ( spl6_51
  <=> ~ r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f1676,plain,
    ( spl6_87
  <=> ~ r1_tarski(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f2970,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl6_52
    | ~ spl6_87 ),
    inference(backward_demodulation,[],[f2882,f1677])).

fof(f1677,plain,
    ( ~ r1_tarski(sK4,sK0)
    | ~ spl6_87 ),
    inference(avatar_component_clause,[],[f1676])).

fof(f3185,plain,
    ( ~ spl6_131
    | ~ spl6_52
    | spl6_63 ),
    inference(avatar_split_clause,[],[f2895,f597,f533,f3183])).

fof(f3183,plain,
    ( spl6_131
  <=> ~ r1_tarski(k1_xboole_0,k10_relat_1(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_131])])).

fof(f597,plain,
    ( spl6_63
  <=> ~ r1_tarski(k1_xboole_0,k10_relat_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f2895,plain,
    ( ~ r1_tarski(k1_xboole_0,k10_relat_1(sK2,k1_xboole_0))
    | ~ spl6_52
    | ~ spl6_63 ),
    inference(backward_demodulation,[],[f2882,f598])).

fof(f598,plain,
    ( ~ r1_tarski(k1_xboole_0,k10_relat_1(sK2,sK4))
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f597])).

fof(f3178,plain,
    ( spl6_128
    | ~ spl6_32
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f2888,f533,f255,f3176])).

fof(f2888,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),k1_xboole_0)
    | ~ spl6_32
    | ~ spl6_52 ),
    inference(backward_demodulation,[],[f2882,f256])).

fof(f3171,plain,
    ( ~ spl6_127
    | spl6_31
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f2886,f533,f240,f3169])).

fof(f2886,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,k1_xboole_0))
    | ~ spl6_31
    | ~ spl6_52 ),
    inference(backward_demodulation,[],[f2882,f241])).

fof(f3163,plain,
    ( spl6_124
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f2882,f533,f3161])).

fof(f3161,plain,
    ( spl6_124
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_124])])).

fof(f3148,plain,
    ( spl6_122
    | ~ spl6_32
    | ~ spl6_52
    | ~ spl6_102 ),
    inference(avatar_split_clause,[],[f3137,f2352,f533,f255,f3146])).

fof(f3146,plain,
    ( spl6_122
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_122])])).

fof(f3137,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl6_32
    | ~ spl6_52
    | ~ spl6_102 ),
    inference(forward_demodulation,[],[f2367,f2882])).

fof(f3139,plain,
    ( ~ spl6_32
    | ~ spl6_52
    | spl6_97
    | ~ spl6_102 ),
    inference(avatar_contradiction_clause,[],[f3138])).

fof(f3138,plain,
    ( $false
    | ~ spl6_32
    | ~ spl6_52
    | ~ spl6_97
    | ~ spl6_102 ),
    inference(subsumption_resolution,[],[f3137,f2979])).

fof(f2979,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl6_52
    | ~ spl6_97 ),
    inference(backward_demodulation,[],[f2882,f2034])).

fof(f2034,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | ~ spl6_97 ),
    inference(avatar_component_clause,[],[f2033])).

fof(f2033,plain,
    ( spl6_97
  <=> ~ r1_tarski(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f3135,plain,
    ( ~ spl6_52
    | spl6_97
    | ~ spl6_108 ),
    inference(avatar_contradiction_clause,[],[f3134])).

fof(f3134,plain,
    ( $false
    | ~ spl6_52
    | ~ spl6_97
    | ~ spl6_108 ),
    inference(subsumption_resolution,[],[f3133,f2979])).

fof(f3133,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl6_52
    | ~ spl6_108 ),
    inference(forward_demodulation,[],[f2459,f2882])).

fof(f3110,plain,
    ( ~ spl6_52
    | spl6_113 ),
    inference(avatar_contradiction_clause,[],[f3109])).

fof(f3109,plain,
    ( $false
    | ~ spl6_52
    | ~ spl6_113 ),
    inference(subsumption_resolution,[],[f3044,f181])).

fof(f3044,plain,
    ( ~ r1_tarski(sK5(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl6_52
    | ~ spl6_113 ),
    inference(backward_demodulation,[],[f2882,f2582])).

fof(f2582,plain,
    ( ~ r1_tarski(sK5(k1_zfmisc_1(k1_xboole_0)),sK4)
    | ~ spl6_113 ),
    inference(avatar_component_clause,[],[f2581])).

fof(f2581,plain,
    ( spl6_113
  <=> ~ r1_tarski(sK5(k1_zfmisc_1(k1_xboole_0)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_113])])).

fof(f3100,plain,
    ( ~ spl6_50
    | ~ spl6_52
    | spl6_87 ),
    inference(avatar_contradiction_clause,[],[f3099])).

fof(f3099,plain,
    ( $false
    | ~ spl6_50
    | ~ spl6_52
    | ~ spl6_87 ),
    inference(subsumption_resolution,[],[f2970,f515])).

fof(f515,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f514])).

fof(f514,plain,
    ( spl6_50
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f2879,plain,
    ( spl6_120
    | ~ spl6_54
    | ~ spl6_110 ),
    inference(avatar_split_clause,[],[f2597,f2547,f536,f2877])).

fof(f2877,plain,
    ( spl6_120
  <=> m1_subset_1(sK5(k9_relat_1(sK2,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).

fof(f2547,plain,
    ( spl6_110
  <=> m1_subset_1(sK5(k9_relat_1(sK2,sK3)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).

fof(f2597,plain,
    ( m1_subset_1(sK5(k9_relat_1(sK2,sK3)),sK1)
    | ~ spl6_54
    | ~ spl6_110 ),
    inference(resolution,[],[f2548,f537])).

fof(f537,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK4)
        | m1_subset_1(X0,sK1) )
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f536])).

fof(f2548,plain,
    ( m1_subset_1(sK5(k9_relat_1(sK2,sK3)),sK4)
    | ~ spl6_110 ),
    inference(avatar_component_clause,[],[f2547])).

fof(f2792,plain,
    ( ~ spl6_119
    | ~ spl6_58
    | spl6_115 ),
    inference(avatar_split_clause,[],[f2714,f2669,f575,f2790])).

fof(f2790,plain,
    ( spl6_119
  <=> ~ r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_119])])).

fof(f575,plain,
    ( spl6_58
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f2669,plain,
    ( spl6_115
  <=> ~ r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_115])])).

fof(f2714,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ spl6_58
    | ~ spl6_115 ),
    inference(resolution,[],[f2670,f2572])).

fof(f2572,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl6_58 ),
    inference(resolution,[],[f576,f71])).

fof(f576,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f575])).

fof(f2670,plain,
    ( ~ r1_tarski(sK3,sK1)
    | ~ spl6_115 ),
    inference(avatar_component_clause,[],[f2669])).

fof(f2774,plain,
    ( spl6_102
    | spl6_104
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f2464,f255,f2355,f2352])).

fof(f2355,plain,
    ( spl6_104
  <=> ! [X0] :
        ( m1_subset_1(X0,sK4)
        | ~ m1_subset_1(X0,k9_relat_1(sK2,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).

fof(f2464,plain,
    ( ! [X2] :
        ( m1_subset_1(X2,sK4)
        | v1_xboole_0(k9_relat_1(sK2,sK3))
        | ~ m1_subset_1(X2,k9_relat_1(sK2,sK3)) )
    | ~ spl6_32 ),
    inference(resolution,[],[f256,f323])).

fof(f2680,plain,
    ( spl6_114
    | ~ spl6_117
    | ~ spl6_24
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f2645,f575,f186,f2678,f2672])).

fof(f2672,plain,
    ( spl6_114
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_114])])).

fof(f2678,plain,
    ( spl6_117
  <=> ~ r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).

fof(f2645,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | r1_tarski(sK3,sK1)
    | ~ spl6_24
    | ~ spl6_58 ),
    inference(resolution,[],[f2590,f187])).

fof(f2590,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,k1_xboole_0)
        | r1_tarski(X1,sK1) )
    | ~ spl6_58 ),
    inference(resolution,[],[f2572,f71])).

fof(f2589,plain,
    ( ~ spl6_108
    | spl6_113 ),
    inference(avatar_contradiction_clause,[],[f2588])).

fof(f2588,plain,
    ( $false
    | ~ spl6_108
    | ~ spl6_113 ),
    inference(subsumption_resolution,[],[f2587,f181])).

fof(f2587,plain,
    ( ~ r1_tarski(sK5(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl6_108
    | ~ spl6_113 ),
    inference(resolution,[],[f2582,f2551])).

fof(f2551,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK4)
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl6_108 ),
    inference(resolution,[],[f2459,f71])).

fof(f2586,plain,
    ( spl6_112
    | ~ spl6_78
    | ~ spl6_102 ),
    inference(avatar_split_clause,[],[f2376,f2352,f877,f2584])).

fof(f2571,plain,
    ( spl6_58
    | ~ spl6_28
    | ~ spl6_108 ),
    inference(avatar_split_clause,[],[f2550,f2458,f220,f575])).

fof(f2550,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl6_28
    | ~ spl6_108 ),
    inference(resolution,[],[f2459,f253])).

fof(f2559,plain,
    ( ~ spl6_28
    | spl6_59
    | ~ spl6_108 ),
    inference(avatar_contradiction_clause,[],[f2558])).

fof(f2558,plain,
    ( $false
    | ~ spl6_28
    | ~ spl6_59
    | ~ spl6_108 ),
    inference(subsumption_resolution,[],[f2550,f579])).

fof(f579,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f578])).

fof(f578,plain,
    ( spl6_59
  <=> ~ r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f2549,plain,
    ( spl6_110
    | ~ spl6_104 ),
    inference(avatar_split_clause,[],[f2523,f2355,f2547])).

fof(f2523,plain,
    ( m1_subset_1(sK5(k9_relat_1(sK2,sK3)),sK4)
    | ~ spl6_104 ),
    inference(resolution,[],[f2356,f84])).

fof(f2356,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k9_relat_1(sK2,sK3))
        | m1_subset_1(X0,sK4) )
    | ~ spl6_104 ),
    inference(avatar_component_clause,[],[f2355])).

fof(f2460,plain,
    ( spl6_108
    | ~ spl6_32
    | ~ spl6_102 ),
    inference(avatar_split_clause,[],[f2367,f2352,f255,f2458])).

fof(f2364,plain,
    ( ~ spl6_107
    | ~ spl6_50
    | spl6_99 ),
    inference(avatar_split_clause,[],[f2345,f2290,f514,f2362])).

fof(f2362,plain,
    ( spl6_107
  <=> ~ r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).

fof(f2290,plain,
    ( spl6_99
  <=> ~ r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).

fof(f2345,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl6_50
    | ~ spl6_99 ),
    inference(resolution,[],[f2291,f605])).

fof(f605,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK0)
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl6_50 ),
    inference(resolution,[],[f515,f71])).

fof(f2291,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ spl6_99 ),
    inference(avatar_component_clause,[],[f2290])).

fof(f2357,plain,
    ( spl6_102
    | spl6_104
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f860,f255,f2355,f2352])).

fof(f860,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK4)
        | v1_xboole_0(k9_relat_1(sK2,sK3))
        | ~ m1_subset_1(X0,k9_relat_1(sK2,sK3)) )
    | ~ spl6_32 ),
    inference(resolution,[],[f256,f323])).

fof(f2301,plain,
    ( spl6_98
    | ~ spl6_101
    | ~ spl6_34
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f1624,f514,f266,f2299,f2293])).

fof(f2293,plain,
    ( spl6_98
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f2299,plain,
    ( spl6_101
  <=> ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).

fof(f266,plain,
    ( spl6_34
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f1624,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | r1_tarski(sK2,sK0)
    | ~ spl6_34
    | ~ spl6_50 ),
    inference(resolution,[],[f620,f267])).

fof(f267,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f266])).

fof(f620,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,k1_xboole_0)
        | r1_tarski(X1,sK0) )
    | ~ spl6_50 ),
    inference(resolution,[],[f605,f71])).

fof(f2035,plain,
    ( ~ spl6_97
    | ~ spl6_50
    | spl6_87 ),
    inference(avatar_split_clause,[],[f1706,f1676,f514,f2033])).

fof(f1706,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | ~ spl6_50
    | ~ spl6_87 ),
    inference(resolution,[],[f1677,f605])).

fof(f1937,plain,
    ( spl6_94
    | ~ spl6_0
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f1725,f1717,f94,f1935])).

fof(f1935,plain,
    ( spl6_94
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f94,plain,
    ( spl6_0
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f1717,plain,
    ( spl6_90
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f1725,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_0
    | ~ spl6_90 ),
    inference(backward_demodulation,[],[f1724,f95])).

fof(f95,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f94])).

fof(f1724,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_90 ),
    inference(resolution,[],[f1718,f87])).

fof(f1718,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_90 ),
    inference(avatar_component_clause,[],[f1717])).

fof(f1722,plain,
    ( spl6_90
    | spl6_92
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f792,f266,f1720,f1717])).

fof(f1720,plain,
    ( spl6_92
  <=> ! [X65] :
        ( m1_subset_1(X65,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X65,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f792,plain,
    ( ! [X65] :
        ( m1_subset_1(X65,k2_zfmisc_1(sK0,sK1))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X65,sK2) )
    | ~ spl6_34 ),
    inference(resolution,[],[f323,f267])).

fof(f1687,plain,
    ( spl6_86
    | ~ spl6_89
    | ~ spl6_28
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f1626,f514,f220,f1685,f1679])).

fof(f1679,plain,
    ( spl6_86
  <=> r1_tarski(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f1685,plain,
    ( spl6_89
  <=> ~ r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).

fof(f1626,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | r1_tarski(sK4,sK0)
    | ~ spl6_28
    | ~ spl6_50 ),
    inference(resolution,[],[f620,f221])).

fof(f1446,plain,
    ( spl6_84
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f1396,f319,f1444])).

fof(f1444,plain,
    ( spl6_84
  <=> r1_tarski(sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK4)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f319,plain,
    ( spl6_42
  <=> r1_tarski(sK5(k1_zfmisc_1(sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f1396,plain,
    ( r1_tarski(sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK4)))),sK1)
    | ~ spl6_42 ),
    inference(resolution,[],[f378,f181])).

fof(f378,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK5(k1_zfmisc_1(sK4)))
        | r1_tarski(X0,sK1) )
    | ~ spl6_42 ),
    inference(resolution,[],[f320,f71])).

fof(f320,plain,
    ( r1_tarski(sK5(k1_zfmisc_1(sK4)),sK1)
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f319])).

fof(f1219,plain,
    ( spl6_82
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f1154,f307,f1217])).

fof(f1217,plain,
    ( spl6_82
  <=> r1_tarski(sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK3)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f307,plain,
    ( spl6_40
  <=> r1_tarski(sK5(k1_zfmisc_1(sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f1154,plain,
    ( r1_tarski(sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK3)))),sK0)
    | ~ spl6_40 ),
    inference(resolution,[],[f370,f181])).

fof(f370,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK5(k1_zfmisc_1(sK3)))
        | r1_tarski(X0,sK0) )
    | ~ spl6_40 ),
    inference(resolution,[],[f308,f71])).

fof(f308,plain,
    ( r1_tarski(sK5(k1_zfmisc_1(sK3)),sK0)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f307])).

fof(f898,plain,
    ( spl6_80
    | ~ spl6_28
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f880,f877,f220,f896])).

fof(f896,plain,
    ( spl6_80
  <=> r1_tarski(sK5(k1_zfmisc_1(k9_relat_1(sK2,sK3))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f880,plain,
    ( r1_tarski(sK5(k1_zfmisc_1(k9_relat_1(sK2,sK3))),sK1)
    | ~ spl6_28
    | ~ spl6_78 ),
    inference(resolution,[],[f878,f253])).

fof(f879,plain,
    ( spl6_78
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f870,f255,f877])).

fof(f870,plain,
    ( r1_tarski(sK5(k1_zfmisc_1(k9_relat_1(sK2,sK3))),sK4)
    | ~ spl6_32 ),
    inference(resolution,[],[f862,f181])).

fof(f862,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k9_relat_1(sK2,sK3))
        | r1_tarski(X2,sK4) )
    | ~ spl6_32 ),
    inference(resolution,[],[f256,f71])).

fof(f858,plain,
    ( spl6_32
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f854,f150,f136,f255])).

fof(f136,plain,
    ( spl6_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f150,plain,
    ( spl6_16
  <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f854,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f151,f250])).

fof(f250,plain,
    ( ! [X16] : k7_relset_1(sK0,sK1,sK2,X16) = k9_relat_1(sK2,X16)
    | ~ spl6_12 ),
    inference(resolution,[],[f77,f137])).

fof(f137,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t172_funct_2.p',redefinition_k7_relset_1)).

fof(f151,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f857,plain,
    ( ~ spl6_31
    | ~ spl6_12
    | spl6_19 ),
    inference(avatar_split_clause,[],[f853,f153,f136,f240])).

fof(f153,plain,
    ( spl6_19
  <=> ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f853,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_12
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f154,f234])).

fof(f234,plain,
    ( ! [X16] : k8_relset_1(sK0,sK1,sK2,X16) = k10_relat_1(sK2,X16)
    | ~ spl6_12 ),
    inference(resolution,[],[f69,f137])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t172_funct_2.p',redefinition_k8_relset_1)).

fof(f154,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f153])).

fof(f856,plain,
    ( ~ spl6_12
    | ~ spl6_16
    | spl6_33 ),
    inference(avatar_contradiction_clause,[],[f855])).

fof(f855,plain,
    ( $false
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f854,f259])).

fof(f259,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl6_33
  <=> ~ r1_tarski(k9_relat_1(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f852,plain,
    ( ~ spl6_0
    | ~ spl6_26
    | ~ spl6_30
    | spl6_33 ),
    inference(avatar_contradiction_clause,[],[f851])).

fof(f851,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_26
    | ~ spl6_30
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f850,f244])).

fof(f244,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl6_30
  <=> r1_tarski(sK3,k10_relat_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f850,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_0
    | ~ spl6_26
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f849,f200])).

fof(f849,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_0
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f834,f95])).

fof(f834,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_33 ),
    inference(resolution,[],[f342,f259])).

fof(f342,plain,(
    ! [X12,X10,X11] :
      ( r1_tarski(k9_relat_1(X10,X11),X12)
      | ~ v1_funct_1(X10)
      | ~ v1_relat_1(X10)
      | ~ r1_tarski(X11,k10_relat_1(X10,X12)) ) ),
    inference(duplicate_literal_removal,[],[f339])).

fof(f339,plain,(
    ! [X12,X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ v1_funct_1(X10)
      | r1_tarski(k9_relat_1(X10,X11),X12)
      | ~ r1_tarski(X11,k10_relat_1(X10,X12))
      | ~ v1_relat_1(X10) ) ),
    inference(resolution,[],[f213,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t172_funct_2.p',t156_relat_1)).

fof(f213,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k9_relat_1(X0,k10_relat_1(X0,X2)))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f76,f71])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t172_funct_2.p',t145_funct_1)).

fof(f816,plain,
    ( spl6_76
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f807,f266,f814])).

fof(f814,plain,
    ( spl6_76
  <=> v1_relat_1(sK5(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f807,plain,
    ( v1_relat_1(sK5(k1_zfmisc_1(sK2)))
    | ~ spl6_34 ),
    inference(resolution,[],[f442,f181])).

fof(f442,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,sK2)
        | v1_relat_1(X4) )
    | ~ spl6_34 ),
    inference(resolution,[],[f270,f190])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f81,f74])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t172_funct_2.p',cc1_relset_1)).

fof(f270,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r1_tarski(X0,sK2) )
    | ~ spl6_34 ),
    inference(resolution,[],[f267,f71])).

fof(f690,plain,
    ( ~ spl6_75
    | ~ spl6_12
    | ~ spl6_18
    | ~ spl6_50
    | spl6_63 ),
    inference(avatar_split_clause,[],[f656,f597,f514,f156,f136,f688])).

fof(f688,plain,
    ( spl6_75
  <=> ~ r1_tarski(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f156,plain,
    ( spl6_18
  <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f656,plain,
    ( ~ r1_tarski(sK0,sK3)
    | ~ spl6_12
    | ~ spl6_18
    | ~ spl6_50
    | ~ spl6_63 ),
    inference(subsumption_resolution,[],[f643,f598])).

fof(f643,plain,
    ( ~ r1_tarski(sK0,sK3)
    | r1_tarski(k1_xboole_0,k10_relat_1(sK2,sK4))
    | ~ spl6_12
    | ~ spl6_18
    | ~ spl6_50 ),
    inference(resolution,[],[f284,f515])).

fof(f284,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,sK3)
        | r1_tarski(X1,k10_relat_1(sK2,sK4)) )
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(resolution,[],[f236,f71])).

fof(f236,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k10_relat_1(sK2,sK4))
        | ~ r1_tarski(X0,sK3) )
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f234,f202])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3)
        | r1_tarski(X0,k8_relset_1(sK0,sK1,sK2,sK4)) )
    | ~ spl6_18 ),
    inference(resolution,[],[f71,f157])).

fof(f157,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f156])).

fof(f679,plain,
    ( spl6_68
    | spl6_72
    | ~ spl6_0
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f459,f136,f129,f94,f677,f666])).

fof(f666,plain,
    ( spl6_68
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f677,plain,
    ( spl6_72
  <=> ! [X1,X0] :
        ( r1_tarski(X1,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f129,plain,
    ( spl6_10
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f459,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = sK1
        | ~ r1_tarski(X1,X0) )
    | ~ spl6_0
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f458,f234])).

fof(f458,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,k8_relset_1(sK0,sK1,sK2,k9_relat_1(sK2,X0)))
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = sK1
        | ~ r1_tarski(X1,X0) )
    | ~ spl6_0
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f457,f130])).

fof(f130,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f457,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,k8_relset_1(sK0,sK1,sK2,k9_relat_1(sK2,X0)))
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = sK1
        | ~ r1_tarski(X1,X0)
        | ~ v1_funct_2(sK2,sK0,sK1) )
    | ~ spl6_0
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f456,f95])).

fof(f456,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,k8_relset_1(sK0,sK1,sK2,k9_relat_1(sK2,X0)))
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = sK1
        | ~ v1_funct_1(sK2)
        | ~ r1_tarski(X1,X0)
        | ~ v1_funct_2(sK2,sK0,sK1) )
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f452,f137])).

fof(f452,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,k8_relset_1(sK0,sK1,sK2,k9_relat_1(sK2,X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = sK1
        | ~ v1_funct_1(sK2)
        | ~ r1_tarski(X1,X0)
        | ~ v1_funct_2(sK2,sK0,sK1) )
    | ~ spl6_12 ),
    inference(superposition,[],[f269,f250])).

fof(f269,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_tarski(X4,k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X3,X1)
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(X4,X3)
      | ~ v1_funct_2(X0,X1,X2) ) ),
    inference(resolution,[],[f67,f71])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X2,X0)
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t172_funct_2.p',t50_funct_2)).

fof(f671,plain,
    ( spl6_68
    | spl6_70
    | ~ spl6_0
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f291,f136,f129,f94,f669,f666])).

fof(f291,plain,
    ( ! [X1] :
        ( r1_tarski(X1,k10_relat_1(sK2,k9_relat_1(sK2,X1)))
        | ~ r1_tarski(X1,sK0)
        | k1_xboole_0 = sK1 )
    | ~ spl6_0
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f290,f250])).

fof(f290,plain,
    ( ! [X1] :
        ( r1_tarski(X1,k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,X1)))
        | ~ r1_tarski(X1,sK0)
        | k1_xboole_0 = sK1 )
    | ~ spl6_0
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f289,f95])).

fof(f289,plain,
    ( ! [X1] :
        ( r1_tarski(X1,k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,X1)))
        | ~ r1_tarski(X1,sK0)
        | k1_xboole_0 = sK1
        | ~ v1_funct_1(sK2) )
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f288,f137])).

fof(f288,plain,
    ( ! [X1] :
        ( r1_tarski(X1,k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r1_tarski(X1,sK0)
        | k1_xboole_0 = sK1
        | ~ v1_funct_1(sK2) )
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f286,f130])).

fof(f286,plain,
    ( ! [X1] :
        ( r1_tarski(X1,k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,X1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r1_tarski(X1,sK0)
        | k1_xboole_0 = sK1
        | ~ v1_funct_1(sK2) )
    | ~ spl6_12 ),
    inference(superposition,[],[f67,f234])).

fof(f633,plain,
    ( spl6_44
    | spl6_46
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f520,f122,f475,f472])).

fof(f472,plain,
    ( spl6_44
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f475,plain,
    ( spl6_46
  <=> ! [X0] :
        ( m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f122,plain,
    ( spl6_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f520,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK0)
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(X0,sK3) )
    | ~ spl6_8 ),
    inference(resolution,[],[f210,f82])).

fof(f210,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK3)
        | m1_subset_1(X4,sK0) )
    | ~ spl6_8 ),
    inference(resolution,[],[f80,f123])).

fof(f123,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f630,plain,
    ( spl6_66
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f619,f536,f628])).

fof(f619,plain,
    ( m1_subset_1(sK5(sK4),sK1)
    | ~ spl6_54 ),
    inference(resolution,[],[f537,f84])).

fof(f613,plain,
    ( ~ spl6_65
    | ~ spl6_12
    | ~ spl6_18
    | spl6_63 ),
    inference(avatar_split_clause,[],[f603,f597,f156,f136,f611])).

fof(f611,plain,
    ( spl6_65
  <=> ~ r1_tarski(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f603,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl6_12
    | ~ spl6_18
    | ~ spl6_63 ),
    inference(resolution,[],[f598,f236])).

fof(f604,plain,
    ( spl6_50
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f595,f503,f514])).

fof(f503,plain,
    ( spl6_48
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f595,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl6_48 ),
    inference(resolution,[],[f504,f75])).

fof(f504,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f503])).

fof(f602,plain,
    ( spl6_62
    | ~ spl6_30
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f485,f472,f243,f600])).

fof(f600,plain,
    ( spl6_62
  <=> r1_tarski(k1_xboole_0,k10_relat_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f485,plain,
    ( r1_tarski(k1_xboole_0,k10_relat_1(sK2,sK4))
    | ~ spl6_30
    | ~ spl6_44 ),
    inference(backward_demodulation,[],[f479,f244])).

fof(f479,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_44 ),
    inference(resolution,[],[f473,f87])).

fof(f473,plain,
    ( v1_xboole_0(sK3)
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f472])).

fof(f592,plain,
    ( ~ spl6_24
    | ~ spl6_44
    | spl6_51 ),
    inference(avatar_contradiction_clause,[],[f591])).

fof(f591,plain,
    ( $false
    | ~ spl6_24
    | ~ spl6_44
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f481,f518])).

fof(f518,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f517])).

fof(f481,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl6_24
    | ~ spl6_44 ),
    inference(backward_demodulation,[],[f479,f187])).

fof(f590,plain,
    ( spl6_60
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f528,f475,f588])).

fof(f588,plain,
    ( spl6_60
  <=> m1_subset_1(sK5(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f528,plain,
    ( m1_subset_1(sK5(sK3),sK0)
    | ~ spl6_46 ),
    inference(resolution,[],[f476,f84])).

fof(f476,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK3)
        | m1_subset_1(X0,sK0) )
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f475])).

fof(f580,plain,
    ( ~ spl6_59
    | spl6_57 ),
    inference(avatar_split_clause,[],[f570,f561,f578])).

fof(f561,plain,
    ( spl6_57
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f570,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | ~ spl6_57 ),
    inference(resolution,[],[f562,f74])).

fof(f562,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f561])).

fof(f566,plain,
    ( spl6_56
    | ~ spl6_6
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f541,f533,f115,f564])).

fof(f564,plain,
    ( spl6_56
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f115,plain,
    ( spl6_6
  <=> m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f541,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl6_6
    | ~ spl6_52 ),
    inference(backward_demodulation,[],[f540,f116])).

fof(f116,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f540,plain,
    ( k1_xboole_0 = sK4
    | ~ spl6_52 ),
    inference(resolution,[],[f534,f87])).

fof(f538,plain,
    ( spl6_52
    | spl6_54
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f272,f115,f536,f533])).

fof(f272,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK1)
        | v1_xboole_0(sK4)
        | ~ m1_subset_1(X0,sK4) )
    | ~ spl6_6 ),
    inference(resolution,[],[f211,f82])).

fof(f211,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,sK4)
        | m1_subset_1(X5,sK1) )
    | ~ spl6_6 ),
    inference(resolution,[],[f80,f116])).

fof(f519,plain,
    ( ~ spl6_51
    | spl6_49 ),
    inference(avatar_split_clause,[],[f509,f500,f517])).

fof(f500,plain,
    ( spl6_49
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f509,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl6_49 ),
    inference(resolution,[],[f501,f74])).

fof(f501,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f500])).

fof(f505,plain,
    ( spl6_48
    | ~ spl6_8
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f480,f472,f122,f503])).

fof(f480,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl6_8
    | ~ spl6_44 ),
    inference(backward_demodulation,[],[f479,f123])).

fof(f477,plain,
    ( spl6_44
    | spl6_46
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f271,f122,f475,f472])).

fof(f271,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK0)
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(X0,sK3) )
    | ~ spl6_8 ),
    inference(resolution,[],[f210,f82])).

fof(f321,plain,
    ( spl6_42
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f302,f220,f319])).

fof(f302,plain,
    ( r1_tarski(sK5(k1_zfmisc_1(sK4)),sK1)
    | ~ spl6_28 ),
    inference(resolution,[],[f181,f253])).

fof(f309,plain,
    ( spl6_40
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f301,f186,f307])).

fof(f301,plain,
    ( r1_tarski(sK5(k1_zfmisc_1(sK3)),sK0)
    | ~ spl6_24 ),
    inference(resolution,[],[f181,f238])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3)
        | r1_tarski(X0,sK0) )
    | ~ spl6_24 ),
    inference(resolution,[],[f187,f71])).

fof(f282,plain,
    ( ~ spl6_37
    | spl6_38
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f204,f136,f280,f277])).

fof(f277,plain,
    ( spl6_37
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f280,plain,
    ( spl6_38
  <=> ! [X3] : ~ r2_hidden(X3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f204,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl6_12 ),
    inference(resolution,[],[f79,f137])).

fof(f268,plain,
    ( spl6_34
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f178,f136,f266])).

fof(f178,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl6_12 ),
    inference(resolution,[],[f75,f137])).

fof(f260,plain,
    ( ~ spl6_33
    | ~ spl6_12
    | spl6_17 ),
    inference(avatar_split_clause,[],[f252,f147,f136,f258])).

fof(f147,plain,
    ( spl6_17
  <=> ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f252,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_12
    | ~ spl6_17 ),
    inference(backward_demodulation,[],[f250,f148])).

fof(f148,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f147])).

fof(f245,plain,
    ( spl6_30
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f237,f156,f136,f243])).

fof(f237,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f234,f157])).

fof(f222,plain,
    ( spl6_28
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f180,f115,f220])).

fof(f180,plain,
    ( r1_tarski(sK4,sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f75,f116])).

fof(f201,plain,
    ( spl6_26
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f191,f136,f199])).

fof(f191,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_12 ),
    inference(resolution,[],[f81,f137])).

fof(f188,plain,
    ( spl6_24
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f179,f122,f186])).

fof(f179,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl6_8 ),
    inference(resolution,[],[f75,f123])).

fof(f176,plain,
    ( spl6_22
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f160,f143,f174])).

fof(f174,plain,
    ( spl6_22
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f143,plain,
    ( spl6_14
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f160,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl6_14 ),
    inference(resolution,[],[f87,f144])).

fof(f144,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f143])).

fof(f168,plain,
    ( spl6_20
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f161,f143,f166])).

fof(f161,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f160,f144])).

fof(f159,plain,
    ( ~ spl6_17
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f59,f153,f147])).

fof(f59,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(X1))
                       => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                        <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(X1))
                     => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t172_funct_2.p',t172_funct_2)).

fof(f158,plain,
    ( spl6_16
    | spl6_18 ),
    inference(avatar_split_clause,[],[f58,f156,f150])).

fof(f58,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f145,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f88,f143])).

fof(f88,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t172_funct_2.p',dt_o_0_0_xboole_0)).

fof(f138,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f64,f136])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f131,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f63,f129])).

fof(f63,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f124,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f61,f122])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f117,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f60,f115])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f110,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f66,f108])).

fof(f108,plain,
    ( spl6_5
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f66,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f103,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f65,f101])).

fof(f101,plain,
    ( spl6_3
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f65,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f96,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f62,f94])).

fof(f62,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------

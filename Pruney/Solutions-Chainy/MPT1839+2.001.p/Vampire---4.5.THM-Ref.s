%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:01 EST 2020

% Result     : Theorem 2.81s
% Output     : Refutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 250 expanded)
%              Number of leaves         :   34 (  78 expanded)
%              Depth                    :   14
%              Number of atoms          :  288 ( 612 expanded)
%              Number of equality atoms :   40 ( 113 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f769,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f264,f274,f275,f277,f550,f711,f768])).

fof(f768,plain,
    ( spl11_3
    | ~ spl11_13 ),
    inference(avatar_contradiction_clause,[],[f767])).

fof(f767,plain,
    ( $false
    | spl11_3
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f765,f113])).

fof(f113,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl11_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f765,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl11_13 ),
    inference(superposition,[],[f639,f380])).

fof(f380,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(backward_demodulation,[],[f238,f379])).

fof(f379,plain,(
    ! [X19,X20] : k3_xboole_0(k2_xboole_0(X19,X20),X19) = X19 ),
    inference(resolution,[],[f269,f291])).

fof(f291,plain,(
    ! [X6,X5] : r1_tarski(X5,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f61,f172])).

fof(f172,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f71,f97])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f61,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f269,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k3_xboole_0(X3,X2) = X2 ) ),
    inference(subsumption_resolution,[],[f267,f97])).

fof(f267,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X2)
      | ~ r1_tarski(X2,X3)
      | k3_xboole_0(X3,X2) = X2 ) ),
    inference(duplicate_literal_removal,[],[f266])).

fof(f266,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X2)
      | ~ r1_tarski(X2,X3)
      | k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X2)
      | ~ r1_tarski(X2,X3)
      | k3_xboole_0(X3,X2) = X2 ) ),
    inference(resolution,[],[f57,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK2(X0,X1,X2),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k3_xboole_0(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK2(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k3_xboole_0(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f238,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f59,f97])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_xboole_1)).

fof(f639,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,X0))
    | ~ spl11_13 ),
    inference(forward_demodulation,[],[f615,f403])).

fof(f403,plain,(
    ! [X23,X22] : k2_xboole_0(X22,k3_xboole_0(X22,X23)) = X22 ),
    inference(superposition,[],[f380,f173])).

fof(f173,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k3_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(resolution,[],[f71,f72])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f615,plain,
    ( ! [X0] : r1_tarski(k2_xboole_0(sK0,k3_xboole_0(sK0,X0)),k2_xboole_0(sK1,X0))
    | ~ spl11_13 ),
    inference(superposition,[],[f60,f549])).

fof(f549,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f547])).

fof(f547,plain,
    ( spl11_13
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f60,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f711,plain,
    ( spl11_14
    | ~ spl11_13 ),
    inference(avatar_split_clause,[],[f638,f547,f708])).

fof(f708,plain,
    ( spl11_14
  <=> sK1 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f638,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl11_13 ),
    inference(superposition,[],[f380,f549])).

fof(f550,plain,
    ( spl11_13
    | ~ spl11_2
    | spl11_4 ),
    inference(avatar_split_clause,[],[f514,f116,f106,f547])).

fof(f106,plain,
    ( spl11_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f116,plain,
    ( spl11_4
  <=> v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f514,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl11_2
    | spl11_4 ),
    inference(subsumption_resolution,[],[f506,f108])).

fof(f108,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f506,plain,
    ( ~ v1_zfmisc_1(sK0)
    | sK0 = k3_xboole_0(sK0,sK1)
    | spl11_4 ),
    inference(resolution,[],[f235,f118])).

fof(f118,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    | spl11_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f235,plain,(
    ! [X2,X1] :
      ( v1_xboole_0(k3_xboole_0(X1,X2))
      | ~ v1_zfmisc_1(X1)
      | k3_xboole_0(X1,X2) = X1 ) ),
    inference(global_subsumption,[],[f71,f169,f230])).

fof(f230,plain,(
    ! [X2,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(k3_xboole_0(X1,X2))
      | k3_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f73,f72])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f169,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f66,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f277,plain,(
    ~ spl11_11 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f273,f270])).

fof(f270,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl11_11 ),
    inference(resolution,[],[f259,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_realset1)).

fof(f259,plain,
    ( ! [X0] : ~ v1_zfmisc_1(X0)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl11_11
  <=> ! [X0] : ~ v1_zfmisc_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f273,plain,
    ( ! [X1] : v1_xboole_0(X1)
    | ~ spl11_11 ),
    inference(resolution,[],[f259,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v1_zfmisc_1(sK6(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_realset1)).

fof(f275,plain,
    ( ~ spl11_2
    | ~ spl11_11 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_11 ),
    inference(resolution,[],[f259,f108])).

fof(f274,plain,
    ( ~ spl11_6
    | ~ spl11_11 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | ~ spl11_6
    | ~ spl11_11 ),
    inference(resolution,[],[f259,f128])).

fof(f128,plain,
    ( v1_zfmisc_1(sK4)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl11_6
  <=> v1_zfmisc_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f264,plain,
    ( spl11_11
    | spl11_12
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f201,f141,f261,f258])).

fof(f261,plain,
    ( spl11_12
  <=> v1_zfmisc_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f141,plain,
    ( spl11_9
  <=> v1_xboole_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f201,plain,
    ( ! [X0] :
        ( v1_zfmisc_1(sK7)
        | ~ v1_zfmisc_1(X0) )
    | ~ spl11_9 ),
    inference(backward_demodulation,[],[f176,f194])).

fof(f194,plain,
    ( ! [X0] : sK7 = sK9(X0)
    | ~ spl11_9 ),
    inference(resolution,[],[f160,f93])).

fof(f93,plain,(
    ! [X0] : v1_xboole_0(sK9(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f160,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK7 = X0 )
    | ~ spl11_9 ),
    inference(resolution,[],[f87,f143])).

fof(f143,plain,
    ( v1_xboole_0(sK7)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f141])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f176,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | v1_zfmisc_1(sK9(X0)) ) ),
    inference(resolution,[],[f79,f92])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(sK9(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_zfmisc_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_zfmisc_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_zfmisc_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_1)).

fof(f149,plain,(
    ~ spl11_10 ),
    inference(avatar_split_clause,[],[f84,f146])).

fof(f146,plain,
    ( spl11_10
  <=> v1_xboole_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f84,plain,(
    ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_xboole_0)).

fof(f144,plain,(
    spl11_9 ),
    inference(avatar_split_clause,[],[f83,f141])).

fof(f83,plain,(
    v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f139,plain,(
    ~ spl11_8 ),
    inference(avatar_split_clause,[],[f77,f136])).

fof(f136,plain,
    ( spl11_8
  <=> v1_zfmisc_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f77,plain,(
    ~ v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ? [X0] :
      ( ~ v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_realset1)).

fof(f134,plain,(
    ~ spl11_7 ),
    inference(avatar_split_clause,[],[f76,f131])).

fof(f131,plain,
    ( spl11_7
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f76,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f129,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f75,f126])).

fof(f75,plain,(
    v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ? [X0] :
      ( v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_realset1)).

fof(f124,plain,(
    ~ spl11_5 ),
    inference(avatar_split_clause,[],[f74,f121])).

fof(f121,plain,
    ( spl11_5
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f74,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f119,plain,(
    ~ spl11_4 ),
    inference(avatar_split_clause,[],[f51,f116])).

fof(f51,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

fof(f114,plain,(
    ~ spl11_3 ),
    inference(avatar_split_clause,[],[f52,f111])).

fof(f52,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f109,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f54,f106])).

fof(f54,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f104,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f53,f101])).

fof(f101,plain,
    ( spl11_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f53,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:55:35 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.51  % (17840)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (17862)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (17854)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (17846)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (17852)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (17845)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (17841)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (17857)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (17849)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (17844)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (17842)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (17843)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (17848)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (17869)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (17850)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (17860)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (17859)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (17863)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (17855)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (17856)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (17867)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (17868)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (17858)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (17864)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (17861)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (17847)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (17851)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (17865)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % (17853)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.57  % (17866)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.81/0.75  % (17841)Refutation found. Thanks to Tanya!
% 2.81/0.75  % SZS status Theorem for theBenchmark
% 2.81/0.75  % SZS output start Proof for theBenchmark
% 2.81/0.75  fof(f769,plain,(
% 2.81/0.75    $false),
% 2.81/0.75    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f264,f274,f275,f277,f550,f711,f768])).
% 2.81/0.75  fof(f768,plain,(
% 2.81/0.75    spl11_3 | ~spl11_13),
% 2.81/0.75    inference(avatar_contradiction_clause,[],[f767])).
% 2.81/0.75  fof(f767,plain,(
% 2.81/0.75    $false | (spl11_3 | ~spl11_13)),
% 2.81/0.75    inference(subsumption_resolution,[],[f765,f113])).
% 2.81/0.75  fof(f113,plain,(
% 2.81/0.75    ~r1_tarski(sK0,sK1) | spl11_3),
% 2.81/0.75    inference(avatar_component_clause,[],[f111])).
% 2.81/0.75  fof(f111,plain,(
% 2.81/0.75    spl11_3 <=> r1_tarski(sK0,sK1)),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 2.81/0.75  fof(f765,plain,(
% 2.81/0.75    r1_tarski(sK0,sK1) | ~spl11_13),
% 2.81/0.75    inference(superposition,[],[f639,f380])).
% 2.81/0.75  fof(f380,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 2.81/0.75    inference(backward_demodulation,[],[f238,f379])).
% 2.81/0.75  fof(f379,plain,(
% 2.81/0.75    ( ! [X19,X20] : (k3_xboole_0(k2_xboole_0(X19,X20),X19) = X19) )),
% 2.81/0.75    inference(resolution,[],[f269,f291])).
% 2.81/0.75  fof(f291,plain,(
% 2.81/0.75    ( ! [X6,X5] : (r1_tarski(X5,k2_xboole_0(X5,X6))) )),
% 2.81/0.75    inference(superposition,[],[f61,f172])).
% 2.81/0.75  fof(f172,plain,(
% 2.81/0.75    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.81/0.75    inference(resolution,[],[f71,f97])).
% 2.81/0.75  fof(f97,plain,(
% 2.81/0.75    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.81/0.75    inference(equality_resolution,[],[f69])).
% 2.81/0.75  fof(f69,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.81/0.75    inference(cnf_transformation,[],[f5])).
% 2.81/0.75  fof(f5,axiom,(
% 2.81/0.75    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.81/0.75  fof(f71,plain,(
% 2.81/0.75    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.81/0.75    inference(cnf_transformation,[],[f41])).
% 2.81/0.75  fof(f41,plain,(
% 2.81/0.75    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.81/0.75    inference(ennf_transformation,[],[f9])).
% 2.81/0.75  fof(f9,axiom,(
% 2.81/0.75    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.81/0.75  fof(f61,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f10])).
% 2.81/0.75  fof(f10,axiom,(
% 2.81/0.75    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).
% 2.81/0.75  fof(f269,plain,(
% 2.81/0.75    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k3_xboole_0(X3,X2) = X2) )),
% 2.81/0.75    inference(subsumption_resolution,[],[f267,f97])).
% 2.81/0.75  fof(f267,plain,(
% 2.81/0.75    ( ! [X2,X3] : (~r1_tarski(X2,X2) | ~r1_tarski(X2,X3) | k3_xboole_0(X3,X2) = X2) )),
% 2.81/0.75    inference(duplicate_literal_removal,[],[f266])).
% 2.81/0.75  fof(f266,plain,(
% 2.81/0.75    ( ! [X2,X3] : (~r1_tarski(X2,X2) | ~r1_tarski(X2,X3) | k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X2) | ~r1_tarski(X2,X3) | k3_xboole_0(X3,X2) = X2) )),
% 2.81/0.75    inference(resolution,[],[f57,f56])).
% 2.81/0.75  fof(f56,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (r1_tarski(sK2(X0,X1,X2),X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | k3_xboole_0(X1,X2) = X0) )),
% 2.81/0.75    inference(cnf_transformation,[],[f35])).
% 2.81/0.75  fof(f35,plain,(
% 2.81/0.75    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.81/0.75    inference(flattening,[],[f34])).
% 2.81/0.75  fof(f34,plain,(
% 2.81/0.75    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.81/0.75    inference(ennf_transformation,[],[f8])).
% 2.81/0.75  fof(f8,axiom,(
% 2.81/0.75    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).
% 2.81/0.75  fof(f57,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (~r1_tarski(sK2(X0,X1,X2),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | k3_xboole_0(X1,X2) = X0) )),
% 2.81/0.75    inference(cnf_transformation,[],[f35])).
% 2.81/0.75  fof(f238,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k2_xboole_0(X0,X1),X0)) )),
% 2.81/0.75    inference(resolution,[],[f59,f97])).
% 2.81/0.75  fof(f59,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f38])).
% 2.81/0.75  fof(f38,plain,(
% 2.81/0.75    ! [X0,X1,X2] : (k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 2.81/0.75    inference(ennf_transformation,[],[f11])).
% 2.81/0.75  fof(f11,axiom,(
% 2.81/0.75    ! [X0,X1,X2] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_xboole_1)).
% 2.81/0.75  fof(f639,plain,(
% 2.81/0.75    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(sK1,X0))) ) | ~spl11_13),
% 2.81/0.75    inference(forward_demodulation,[],[f615,f403])).
% 2.81/0.75  fof(f403,plain,(
% 2.81/0.75    ( ! [X23,X22] : (k2_xboole_0(X22,k3_xboole_0(X22,X23)) = X22) )),
% 2.81/0.75    inference(superposition,[],[f380,f173])).
% 2.81/0.75  fof(f173,plain,(
% 2.81/0.75    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k3_xboole_0(k3_xboole_0(X1,X2),X1)) )),
% 2.81/0.75    inference(resolution,[],[f71,f72])).
% 2.81/0.75  fof(f72,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f6])).
% 2.81/0.75  fof(f6,axiom,(
% 2.81/0.75    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.81/0.75  fof(f615,plain,(
% 2.81/0.75    ( ! [X0] : (r1_tarski(k2_xboole_0(sK0,k3_xboole_0(sK0,X0)),k2_xboole_0(sK1,X0))) ) | ~spl11_13),
% 2.81/0.75    inference(superposition,[],[f60,f549])).
% 2.81/0.75  fof(f549,plain,(
% 2.81/0.75    sK0 = k3_xboole_0(sK0,sK1) | ~spl11_13),
% 2.81/0.75    inference(avatar_component_clause,[],[f547])).
% 2.81/0.75  fof(f547,plain,(
% 2.81/0.75    spl11_13 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 2.81/0.75  fof(f60,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f12])).
% 2.81/0.75  fof(f12,axiom,(
% 2.81/0.75    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 2.81/0.75  fof(f711,plain,(
% 2.81/0.75    spl11_14 | ~spl11_13),
% 2.81/0.75    inference(avatar_split_clause,[],[f638,f547,f708])).
% 2.81/0.75  fof(f708,plain,(
% 2.81/0.75    spl11_14 <=> sK1 = k2_xboole_0(sK1,sK0)),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 2.81/0.75  fof(f638,plain,(
% 2.81/0.75    sK1 = k2_xboole_0(sK1,sK0) | ~spl11_13),
% 2.81/0.75    inference(superposition,[],[f380,f549])).
% 2.81/0.75  fof(f550,plain,(
% 2.81/0.75    spl11_13 | ~spl11_2 | spl11_4),
% 2.81/0.75    inference(avatar_split_clause,[],[f514,f116,f106,f547])).
% 2.81/0.75  fof(f106,plain,(
% 2.81/0.75    spl11_2 <=> v1_zfmisc_1(sK0)),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 2.81/0.75  fof(f116,plain,(
% 2.81/0.75    spl11_4 <=> v1_xboole_0(k3_xboole_0(sK0,sK1))),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 2.81/0.75  fof(f514,plain,(
% 2.81/0.75    sK0 = k3_xboole_0(sK0,sK1) | (~spl11_2 | spl11_4)),
% 2.81/0.75    inference(subsumption_resolution,[],[f506,f108])).
% 2.81/0.75  fof(f108,plain,(
% 2.81/0.75    v1_zfmisc_1(sK0) | ~spl11_2),
% 2.81/0.75    inference(avatar_component_clause,[],[f106])).
% 2.81/0.75  fof(f506,plain,(
% 2.81/0.75    ~v1_zfmisc_1(sK0) | sK0 = k3_xboole_0(sK0,sK1) | spl11_4),
% 2.81/0.75    inference(resolution,[],[f235,f118])).
% 2.81/0.75  fof(f118,plain,(
% 2.81/0.75    ~v1_xboole_0(k3_xboole_0(sK0,sK1)) | spl11_4),
% 2.81/0.75    inference(avatar_component_clause,[],[f116])).
% 2.81/0.75  fof(f235,plain,(
% 2.81/0.75    ( ! [X2,X1] : (v1_xboole_0(k3_xboole_0(X1,X2)) | ~v1_zfmisc_1(X1) | k3_xboole_0(X1,X2) = X1) )),
% 2.81/0.75    inference(global_subsumption,[],[f71,f169,f230])).
% 2.81/0.75  fof(f230,plain,(
% 2.81/0.75    ( ! [X2,X1] : (v1_xboole_0(X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(k3_xboole_0(X1,X2)) | k3_xboole_0(X1,X2) = X1) )),
% 2.81/0.75    inference(resolution,[],[f73,f72])).
% 2.81/0.75  fof(f73,plain,(
% 2.81/0.75    ( ! [X0,X1] : (~r1_tarski(X0,X1) | v1_xboole_0(X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X0) | X0 = X1) )),
% 2.81/0.75    inference(cnf_transformation,[],[f43])).
% 2.81/0.75  fof(f43,plain,(
% 2.81/0.75    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.81/0.75    inference(flattening,[],[f42])).
% 2.81/0.75  fof(f42,plain,(
% 2.81/0.75    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.81/0.75    inference(ennf_transformation,[],[f29])).
% 2.81/0.75  fof(f29,axiom,(
% 2.81/0.75    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 2.81/0.75  fof(f169,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 2.81/0.75    inference(resolution,[],[f66,f86])).
% 2.81/0.75  fof(f86,plain,(
% 2.81/0.75    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f48])).
% 2.81/0.75  fof(f48,plain,(
% 2.81/0.75    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 2.81/0.75    inference(ennf_transformation,[],[f13])).
% 2.81/0.75  fof(f13,axiom,(
% 2.81/0.75    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 2.81/0.75  fof(f66,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f40])).
% 2.81/0.75  fof(f40,plain,(
% 2.81/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.81/0.75    inference(ennf_transformation,[],[f2])).
% 2.81/0.75  fof(f2,axiom,(
% 2.81/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.81/0.75  fof(f277,plain,(
% 2.81/0.75    ~spl11_11),
% 2.81/0.75    inference(avatar_contradiction_clause,[],[f276])).
% 2.81/0.75  fof(f276,plain,(
% 2.81/0.75    $false | ~spl11_11),
% 2.81/0.75    inference(subsumption_resolution,[],[f273,f270])).
% 2.81/0.75  fof(f270,plain,(
% 2.81/0.75    ( ! [X0] : (~v1_xboole_0(X0)) ) | ~spl11_11),
% 2.81/0.75    inference(resolution,[],[f259,f78])).
% 2.81/0.75  fof(f78,plain,(
% 2.81/0.75    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f44])).
% 2.81/0.75  fof(f44,plain,(
% 2.81/0.75    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 2.81/0.75    inference(ennf_transformation,[],[f24])).
% 2.81/0.75  fof(f24,axiom,(
% 2.81/0.75    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_realset1)).
% 2.81/0.75  fof(f259,plain,(
% 2.81/0.75    ( ! [X0] : (~v1_zfmisc_1(X0)) ) | ~spl11_11),
% 2.81/0.75    inference(avatar_component_clause,[],[f258])).
% 2.81/0.75  fof(f258,plain,(
% 2.81/0.75    spl11_11 <=> ! [X0] : ~v1_zfmisc_1(X0)),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 2.81/0.75  fof(f273,plain,(
% 2.81/0.75    ( ! [X1] : (v1_xboole_0(X1)) ) | ~spl11_11),
% 2.81/0.75    inference(resolution,[],[f259,f82])).
% 2.81/0.75  fof(f82,plain,(
% 2.81/0.75    ( ! [X0] : (v1_zfmisc_1(sK6(X0)) | v1_xboole_0(X0)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f46])).
% 2.81/0.75  fof(f46,plain,(
% 2.81/0.75    ! [X0] : (? [X1] : (v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.81/0.75    inference(ennf_transformation,[],[f28])).
% 2.81/0.75  fof(f28,axiom,(
% 2.81/0.75    ! [X0] : (~v1_xboole_0(X0) => ? [X1] : (v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_realset1)).
% 2.81/0.75  fof(f275,plain,(
% 2.81/0.75    ~spl11_2 | ~spl11_11),
% 2.81/0.75    inference(avatar_contradiction_clause,[],[f271])).
% 2.81/0.75  fof(f271,plain,(
% 2.81/0.75    $false | (~spl11_2 | ~spl11_11)),
% 2.81/0.75    inference(resolution,[],[f259,f108])).
% 2.81/0.75  fof(f274,plain,(
% 2.81/0.75    ~spl11_6 | ~spl11_11),
% 2.81/0.75    inference(avatar_contradiction_clause,[],[f272])).
% 2.81/0.75  fof(f272,plain,(
% 2.81/0.75    $false | (~spl11_6 | ~spl11_11)),
% 2.81/0.75    inference(resolution,[],[f259,f128])).
% 2.81/0.75  fof(f128,plain,(
% 2.81/0.75    v1_zfmisc_1(sK4) | ~spl11_6),
% 2.81/0.75    inference(avatar_component_clause,[],[f126])).
% 2.81/0.75  fof(f126,plain,(
% 2.81/0.75    spl11_6 <=> v1_zfmisc_1(sK4)),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 2.81/0.75  fof(f264,plain,(
% 2.81/0.75    spl11_11 | spl11_12 | ~spl11_9),
% 2.81/0.75    inference(avatar_split_clause,[],[f201,f141,f261,f258])).
% 2.81/0.75  fof(f261,plain,(
% 2.81/0.75    spl11_12 <=> v1_zfmisc_1(sK7)),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 2.81/0.75  fof(f141,plain,(
% 2.81/0.75    spl11_9 <=> v1_xboole_0(sK7)),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 2.81/0.75  fof(f201,plain,(
% 2.81/0.75    ( ! [X0] : (v1_zfmisc_1(sK7) | ~v1_zfmisc_1(X0)) ) | ~spl11_9),
% 2.81/0.75    inference(backward_demodulation,[],[f176,f194])).
% 2.81/0.75  fof(f194,plain,(
% 2.81/0.75    ( ! [X0] : (sK7 = sK9(X0)) ) | ~spl11_9),
% 2.81/0.75    inference(resolution,[],[f160,f93])).
% 2.81/0.75  fof(f93,plain,(
% 2.81/0.75    ( ! [X0] : (v1_xboole_0(sK9(X0))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f18])).
% 2.81/0.75  fof(f18,axiom,(
% 2.81/0.75    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).
% 2.81/0.75  fof(f160,plain,(
% 2.81/0.75    ( ! [X0] : (~v1_xboole_0(X0) | sK7 = X0) ) | ~spl11_9),
% 2.81/0.75    inference(resolution,[],[f87,f143])).
% 2.81/0.75  fof(f143,plain,(
% 2.81/0.75    v1_xboole_0(sK7) | ~spl11_9),
% 2.81/0.75    inference(avatar_component_clause,[],[f141])).
% 2.81/0.75  fof(f87,plain,(
% 2.81/0.75    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f49])).
% 2.81/0.75  fof(f49,plain,(
% 2.81/0.75    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.81/0.75    inference(ennf_transformation,[],[f14])).
% 2.81/0.75  fof(f14,axiom,(
% 2.81/0.75    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 2.81/0.75  fof(f176,plain,(
% 2.81/0.75    ( ! [X0] : (~v1_zfmisc_1(X0) | v1_zfmisc_1(sK9(X0))) )),
% 2.81/0.75    inference(resolution,[],[f79,f92])).
% 2.81/0.75  fof(f92,plain,(
% 2.81/0.75    ( ! [X0] : (m1_subset_1(sK9(X0),k1_zfmisc_1(X0))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f18])).
% 2.81/0.75  fof(f79,plain,(
% 2.81/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_zfmisc_1(X1)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f45])).
% 2.81/0.75  fof(f45,plain,(
% 2.81/0.75    ! [X0] : (! [X1] : (v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0))),
% 2.81/0.75    inference(ennf_transformation,[],[f22])).
% 2.81/0.75  fof(f22,axiom,(
% 2.81/0.75    ! [X0] : (v1_zfmisc_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_zfmisc_1(X1)))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_1)).
% 2.81/0.75  fof(f149,plain,(
% 2.81/0.75    ~spl11_10),
% 2.81/0.75    inference(avatar_split_clause,[],[f84,f146])).
% 2.81/0.75  fof(f146,plain,(
% 2.81/0.75    spl11_10 <=> v1_xboole_0(sK8)),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 2.81/0.75  fof(f84,plain,(
% 2.81/0.75    ~v1_xboole_0(sK8)),
% 2.81/0.75    inference(cnf_transformation,[],[f4])).
% 2.81/0.75  fof(f4,axiom,(
% 2.81/0.75    ? [X0] : ~v1_xboole_0(X0)),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_xboole_0)).
% 2.81/0.75  fof(f144,plain,(
% 2.81/0.75    spl11_9),
% 2.81/0.75    inference(avatar_split_clause,[],[f83,f141])).
% 2.81/0.75  fof(f83,plain,(
% 2.81/0.75    v1_xboole_0(sK7)),
% 2.81/0.75    inference(cnf_transformation,[],[f3])).
% 2.81/0.75  fof(f3,axiom,(
% 2.81/0.75    ? [X0] : v1_xboole_0(X0)),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 2.81/0.75  fof(f139,plain,(
% 2.81/0.75    ~spl11_8),
% 2.81/0.75    inference(avatar_split_clause,[],[f77,f136])).
% 2.81/0.75  fof(f136,plain,(
% 2.81/0.75    spl11_8 <=> v1_zfmisc_1(sK5)),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 2.81/0.75  fof(f77,plain,(
% 2.81/0.75    ~v1_zfmisc_1(sK5)),
% 2.81/0.75    inference(cnf_transformation,[],[f27])).
% 2.81/0.75  fof(f27,axiom,(
% 2.81/0.75    ? [X0] : (~v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_realset1)).
% 2.81/0.75  fof(f134,plain,(
% 2.81/0.75    ~spl11_7),
% 2.81/0.75    inference(avatar_split_clause,[],[f76,f131])).
% 2.81/0.75  fof(f131,plain,(
% 2.81/0.75    spl11_7 <=> v1_xboole_0(sK5)),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 2.81/0.75  fof(f76,plain,(
% 2.81/0.75    ~v1_xboole_0(sK5)),
% 2.81/0.75    inference(cnf_transformation,[],[f27])).
% 2.81/0.75  fof(f129,plain,(
% 2.81/0.75    spl11_6),
% 2.81/0.75    inference(avatar_split_clause,[],[f75,f126])).
% 2.81/0.75  fof(f75,plain,(
% 2.81/0.75    v1_zfmisc_1(sK4)),
% 2.81/0.75    inference(cnf_transformation,[],[f26])).
% 2.81/0.75  fof(f26,axiom,(
% 2.81/0.75    ? [X0] : (v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_realset1)).
% 2.81/0.75  fof(f124,plain,(
% 2.81/0.75    ~spl11_5),
% 2.81/0.75    inference(avatar_split_clause,[],[f74,f121])).
% 2.81/0.75  fof(f121,plain,(
% 2.81/0.75    spl11_5 <=> v1_xboole_0(sK4)),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 2.81/0.75  fof(f74,plain,(
% 2.81/0.75    ~v1_xboole_0(sK4)),
% 2.81/0.75    inference(cnf_transformation,[],[f26])).
% 2.81/0.75  fof(f119,plain,(
% 2.81/0.75    ~spl11_4),
% 2.81/0.75    inference(avatar_split_clause,[],[f51,f116])).
% 2.81/0.75  fof(f51,plain,(
% 2.81/0.75    ~v1_xboole_0(k3_xboole_0(sK0,sK1))),
% 2.81/0.75    inference(cnf_transformation,[],[f33])).
% 2.81/0.75  fof(f33,plain,(
% 2.81/0.75    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 2.81/0.75    inference(flattening,[],[f32])).
% 2.81/0.75  fof(f32,plain,(
% 2.81/0.75    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 2.81/0.75    inference(ennf_transformation,[],[f31])).
% 2.81/0.75  fof(f31,negated_conjecture,(
% 2.81/0.75    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 2.81/0.75    inference(negated_conjecture,[],[f30])).
% 2.81/0.75  fof(f30,conjecture,(
% 2.81/0.75    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).
% 2.81/0.75  fof(f114,plain,(
% 2.81/0.75    ~spl11_3),
% 2.81/0.75    inference(avatar_split_clause,[],[f52,f111])).
% 2.81/0.75  fof(f52,plain,(
% 2.81/0.75    ~r1_tarski(sK0,sK1)),
% 2.81/0.75    inference(cnf_transformation,[],[f33])).
% 2.81/0.75  fof(f109,plain,(
% 2.81/0.75    spl11_2),
% 2.81/0.75    inference(avatar_split_clause,[],[f54,f106])).
% 2.81/0.75  fof(f54,plain,(
% 2.81/0.75    v1_zfmisc_1(sK0)),
% 2.81/0.75    inference(cnf_transformation,[],[f33])).
% 2.81/0.75  fof(f104,plain,(
% 2.81/0.75    ~spl11_1),
% 2.81/0.75    inference(avatar_split_clause,[],[f53,f101])).
% 2.81/0.75  fof(f101,plain,(
% 2.81/0.75    spl11_1 <=> v1_xboole_0(sK0)),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 2.81/0.75  fof(f53,plain,(
% 2.81/0.75    ~v1_xboole_0(sK0)),
% 2.81/0.75    inference(cnf_transformation,[],[f33])).
% 2.81/0.75  % SZS output end Proof for theBenchmark
% 2.81/0.75  % (17841)------------------------------
% 2.81/0.75  % (17841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.75  % (17841)Termination reason: Refutation
% 2.81/0.75  
% 2.81/0.75  % (17841)Memory used [KB]: 6780
% 2.81/0.75  % (17841)Time elapsed: 0.337 s
% 2.81/0.75  % (17841)------------------------------
% 2.81/0.75  % (17841)------------------------------
% 2.81/0.75  % (17839)Success in time 0.384 s
%------------------------------------------------------------------------------

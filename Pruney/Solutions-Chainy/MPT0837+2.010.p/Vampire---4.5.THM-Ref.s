%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 174 expanded)
%              Number of leaves         :   20 (  70 expanded)
%              Depth                    :    8
%              Number of atoms          :  247 ( 474 expanded)
%              Number of equality atoms :   15 (  34 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f50,f60,f67,f74,f78,f90,f97,f100,f106,f116,f121,f133,f142,f166,f171])).

fof(f171,plain,
    ( ~ spl8_11
    | ~ spl8_17
    | ~ spl8_21 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl8_11
    | ~ spl8_17
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f167,f141])).

fof(f141,plain,
    ( m1_subset_1(sK7(sK2,sK1,sK3),sK1)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl8_17
  <=> m1_subset_1(sK7(sK2,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f167,plain,
    ( ~ m1_subset_1(sK7(sK2,sK1,sK3),sK1)
    | ~ spl8_11
    | ~ spl8_21 ),
    inference(resolution,[],[f165,f96])).

fof(f96,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl8_11
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,sK1)
        | ~ r2_hidden(k4_tarski(X4,sK3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f165,plain,
    ( r2_hidden(k4_tarski(sK7(sK2,sK1,sK3),sK3),sK2)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl8_21
  <=> r2_hidden(k4_tarski(sK7(sK2,sK1,sK3),sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f166,plain,
    ( spl8_21
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f122,f104,f164])).

fof(f104,plain,
    ( spl8_12
  <=> sP6(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f122,plain,
    ( r2_hidden(k4_tarski(sK7(sK2,sK1,sK3),sK3),sK2)
    | ~ spl8_12 ),
    inference(resolution,[],[f105,f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(k4_tarski(sK7(X0,X1,X3),X3),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(f105,plain,
    ( sP6(sK3,sK1,sK2)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f104])).

fof(f142,plain,
    ( spl8_17
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f134,f131,f140])).

fof(f131,plain,
    ( spl8_15
  <=> r2_hidden(sK7(sK2,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f134,plain,
    ( m1_subset_1(sK7(sK2,sK1,sK3),sK1)
    | ~ spl8_15 ),
    inference(resolution,[],[f132,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f132,plain,
    ( r2_hidden(sK7(sK2,sK1,sK3),sK1)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f131])).

fof(f133,plain,
    ( spl8_15
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f123,f104,f131])).

fof(f123,plain,
    ( r2_hidden(sK7(sK2,sK1,sK3),sK1)
    | ~ spl8_12 ),
    inference(resolution,[],[f105,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(sK7(X0,X1,X3),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f121,plain,
    ( spl8_12
    | ~ spl8_4
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f120,f88,f58,f104])).

fof(f58,plain,
    ( spl8_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f88,plain,
    ( spl8_10
  <=> r2_hidden(sK3,k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f120,plain,
    ( sP6(sK3,sK1,sK2)
    | ~ spl8_4
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f118,f59])).

fof(f59,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f118,plain,
    ( sP6(sK3,sK1,sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_10 ),
    inference(resolution,[],[f89,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | sP6(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f89,plain,
    ( r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f116,plain,
    ( ~ spl8_4
    | spl8_10
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl8_4
    | spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f114,f99])).

fof(f99,plain,
    ( ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f114,plain,
    ( r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f113,f59])).

fof(f113,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ spl8_12 ),
    inference(resolution,[],[f105,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f106,plain,
    ( spl8_12
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f102,f76,f72,f104])).

fof(f72,plain,
    ( spl8_7
  <=> r2_hidden(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f76,plain,
    ( spl8_8
  <=> r2_hidden(k4_tarski(sK4,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f102,plain,
    ( sP6(sK3,sK1,sK2)
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(resolution,[],[f91,f73])).

fof(f73,plain,
    ( r2_hidden(sK4,sK1)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4,X0)
        | sP6(sK3,X0,sK2) )
    | ~ spl8_8 ),
    inference(resolution,[],[f77,f24])).

fof(f24,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f77,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f76])).

fof(f100,plain,
    ( ~ spl8_10
    | ~ spl8_3
    | spl8_5 ),
    inference(avatar_split_clause,[],[f98,f62,f48,f88])).

fof(f48,plain,
    ( spl8_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f62,plain,
    ( spl8_5
  <=> r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f98,plain,
    ( ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ spl8_3
    | spl8_5 ),
    inference(forward_demodulation,[],[f93,f56])).

fof(f56,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k9_relat_1(sK2,sK1)
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f53,f51])).

fof(f51,plain,
    ( ! [X0] : k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl8_3 ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f49,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f53,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k7_relset_1(sK1,sK0,sK2,sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f49,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f93,plain,
    ( ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | spl8_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f97,plain,
    ( ~ spl8_5
    | spl8_11 ),
    inference(avatar_split_clause,[],[f18,f95,f62])).

fof(f18,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <~> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ! [X3] :
                    ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ! [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <=> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

fof(f90,plain,
    ( spl8_10
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f86,f62,f48,f88])).

fof(f86,plain,
    ( r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f63,f56])).

fof(f63,plain,
    ( r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f78,plain,
    ( spl8_5
    | spl8_8 ),
    inference(avatar_split_clause,[],[f20,f76,f62])).

fof(f20,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f74,plain,
    ( spl8_7
    | spl8_1
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f70,f65,f40,f72])).

fof(f40,plain,
    ( spl8_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f65,plain,
    ( spl8_6
  <=> m1_subset_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f70,plain,
    ( r2_hidden(sK4,sK1)
    | spl8_1
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f69,f41])).

fof(f41,plain,
    ( ~ v1_xboole_0(sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f69,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK4,sK1)
    | ~ spl8_6 ),
    inference(resolution,[],[f66,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f66,plain,
    ( m1_subset_1(sK4,sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f67,plain,
    ( spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f19,f65,f62])).

fof(f19,plain,
    ( m1_subset_1(sK4,sK1)
    | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,
    ( spl8_4
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f52,f48,f58])).

fof(f52,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f50,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f21,f48])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f22,f40])).

fof(f22,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:19:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (12843)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.47  % (12831)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (12831)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (12834)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (12840)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f172,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f42,f50,f60,f67,f74,f78,f90,f97,f100,f106,f116,f121,f133,f142,f166,f171])).
% 0.22/0.48  fof(f171,plain,(
% 0.22/0.48    ~spl8_11 | ~spl8_17 | ~spl8_21),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f170])).
% 0.22/0.48  fof(f170,plain,(
% 0.22/0.48    $false | (~spl8_11 | ~spl8_17 | ~spl8_21)),
% 0.22/0.48    inference(subsumption_resolution,[],[f167,f141])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    m1_subset_1(sK7(sK2,sK1,sK3),sK1) | ~spl8_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f140])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    spl8_17 <=> m1_subset_1(sK7(sK2,sK1,sK3),sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.22/0.48  fof(f167,plain,(
% 0.22/0.48    ~m1_subset_1(sK7(sK2,sK1,sK3),sK1) | (~spl8_11 | ~spl8_21)),
% 0.22/0.48    inference(resolution,[],[f165,f96])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) ) | ~spl8_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f95])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    spl8_11 <=> ! [X4] : (~m1_subset_1(X4,sK1) | ~r2_hidden(k4_tarski(X4,sK3),sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK7(sK2,sK1,sK3),sK3),sK2) | ~spl8_21),
% 0.22/0.48    inference(avatar_component_clause,[],[f164])).
% 0.22/0.48  fof(f164,plain,(
% 0.22/0.48    spl8_21 <=> r2_hidden(k4_tarski(sK7(sK2,sK1,sK3),sK3),sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.22/0.48  fof(f166,plain,(
% 0.22/0.48    spl8_21 | ~spl8_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f122,f104,f164])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    spl8_12 <=> sP6(sK3,sK1,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK7(sK2,sK1,sK3),sK3),sK2) | ~spl8_12),
% 0.22/0.48    inference(resolution,[],[f105,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(k4_tarski(sK7(X0,X1,X3),X3),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    sP6(sK3,sK1,sK2) | ~spl8_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f104])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    spl8_17 | ~spl8_15),
% 0.22/0.48    inference(avatar_split_clause,[],[f134,f131,f140])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    spl8_15 <=> r2_hidden(sK7(sK2,sK1,sK3),sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    m1_subset_1(sK7(sK2,sK1,sK3),sK1) | ~spl8_15),
% 0.22/0.48    inference(resolution,[],[f132,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    r2_hidden(sK7(sK2,sK1,sK3),sK1) | ~spl8_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f131])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    spl8_15 | ~spl8_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f123,f104,f131])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    r2_hidden(sK7(sK2,sK1,sK3),sK1) | ~spl8_12),
% 0.22/0.48    inference(resolution,[],[f105,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(sK7(X0,X1,X3),X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    spl8_12 | ~spl8_4 | ~spl8_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f120,f88,f58,f104])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    spl8_4 <=> v1_relat_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    spl8_10 <=> r2_hidden(sK3,k9_relat_1(sK2,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    sP6(sK3,sK1,sK2) | (~spl8_4 | ~spl8_10)),
% 0.22/0.48    inference(subsumption_resolution,[],[f118,f59])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    v1_relat_1(sK2) | ~spl8_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f58])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    sP6(sK3,sK1,sK2) | ~v1_relat_1(sK2) | ~spl8_10),
% 0.22/0.48    inference(resolution,[],[f89,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (~r2_hidden(X3,k9_relat_1(X0,X1)) | sP6(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    r2_hidden(sK3,k9_relat_1(sK2,sK1)) | ~spl8_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f88])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    ~spl8_4 | spl8_10 | ~spl8_12),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f115])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    $false | (~spl8_4 | spl8_10 | ~spl8_12)),
% 0.22/0.48    inference(subsumption_resolution,[],[f114,f99])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | spl8_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f88])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    r2_hidden(sK3,k9_relat_1(sK2,sK1)) | (~spl8_4 | ~spl8_12)),
% 0.22/0.48    inference(subsumption_resolution,[],[f113,f59])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    ~v1_relat_1(sK2) | r2_hidden(sK3,k9_relat_1(sK2,sK1)) | ~spl8_12),
% 0.22/0.48    inference(resolution,[],[f105,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | ~v1_relat_1(X0) | r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.22/0.48    inference(equality_resolution,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~sP6(X3,X1,X0) | r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    spl8_12 | ~spl8_7 | ~spl8_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f102,f76,f72,f104])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    spl8_7 <=> r2_hidden(sK4,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    spl8_8 <=> r2_hidden(k4_tarski(sK4,sK3),sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    sP6(sK3,sK1,sK2) | (~spl8_7 | ~spl8_8)),
% 0.22/0.48    inference(resolution,[],[f91,f73])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    r2_hidden(sK4,sK1) | ~spl8_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f72])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(sK4,X0) | sP6(sK3,X0,sK2)) ) | ~spl8_8),
% 0.22/0.48    inference(resolution,[],[f77,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(X4,X1) | sP6(X3,X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK4,sK3),sK2) | ~spl8_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f76])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    ~spl8_10 | ~spl8_3 | spl8_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f98,f62,f48,f88])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    spl8_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl8_5 <=> r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | (~spl8_3 | spl8_5)),
% 0.22/0.48    inference(forward_demodulation,[],[f93,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    k2_relset_1(sK1,sK0,sK2) = k9_relat_1(sK2,sK1) | ~spl8_3),
% 0.22/0.48    inference(forward_demodulation,[],[f53,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0] : (k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0)) ) | ~spl8_3),
% 0.22/0.48    inference(resolution,[],[f49,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl8_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f48])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    k2_relset_1(sK1,sK0,sK2) = k7_relset_1(sK1,sK0,sK2,sK1) | ~spl8_3),
% 0.22/0.48    inference(resolution,[],[f49,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) | spl8_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f62])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    ~spl8_5 | spl8_11),
% 0.22/0.48    inference(avatar_split_clause,[],[f18,f95,f62])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X4] : (~m1_subset_1(X4,sK1) | ~r2_hidden(k4_tarski(X4,sK3),sK2) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.22/0.48    inference(negated_conjecture,[],[f8])).
% 0.22/0.48  fof(f8,conjecture,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    spl8_10 | ~spl8_3 | ~spl8_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f86,f62,f48,f88])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    r2_hidden(sK3,k9_relat_1(sK2,sK1)) | (~spl8_3 | ~spl8_5)),
% 0.22/0.48    inference(forward_demodulation,[],[f63,f56])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) | ~spl8_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f62])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    spl8_5 | spl8_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f20,f76,f62])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK4,sK3),sK2) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    spl8_7 | spl8_1 | ~spl8_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f70,f65,f40,f72])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    spl8_1 <=> v1_xboole_0(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    spl8_6 <=> m1_subset_1(sK4,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    r2_hidden(sK4,sK1) | (spl8_1 | ~spl8_6)),
% 0.22/0.48    inference(subsumption_resolution,[],[f69,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ~v1_xboole_0(sK1) | spl8_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f40])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    v1_xboole_0(sK1) | r2_hidden(sK4,sK1) | ~spl8_6),
% 0.22/0.48    inference(resolution,[],[f66,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    m1_subset_1(sK4,sK1) | ~spl8_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f65])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl8_5 | spl8_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f65,f62])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    m1_subset_1(sK4,sK1) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    spl8_4 | ~spl8_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f52,f48,f58])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    v1_relat_1(sK2) | ~spl8_3),
% 0.22/0.48    inference(resolution,[],[f49,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    spl8_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f21,f48])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ~spl8_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f22,f40])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ~v1_xboole_0(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (12831)------------------------------
% 0.22/0.48  % (12831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (12831)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (12831)Memory used [KB]: 6268
% 0.22/0.48  % (12831)Time elapsed: 0.058 s
% 0.22/0.48  % (12831)------------------------------
% 0.22/0.48  % (12831)------------------------------
% 0.22/0.49  % (12830)Success in time 0.124 s
%------------------------------------------------------------------------------

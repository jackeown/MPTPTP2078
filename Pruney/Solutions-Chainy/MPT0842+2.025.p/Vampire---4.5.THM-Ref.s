%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 184 expanded)
%              Number of leaves         :   22 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  311 ( 555 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f79,f93,f99,f106,f114,f124,f132,f136,f150,f153,f157,f161,f193])).

fof(f193,plain,
    ( ~ spl10_11
    | ~ spl10_12
    | ~ spl10_15
    | ~ spl10_17 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_15
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f191,f144])).

fof(f144,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl10_17
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f191,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_15
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f190,f113])).

fof(f113,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl10_12
  <=> r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f190,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl10_11
    | ~ spl10_15
    | ~ spl10_17 ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_11
    | ~ spl10_15
    | ~ spl10_17 ),
    inference(resolution,[],[f188,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f188,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) )
    | ~ spl10_11
    | ~ spl10_15
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f179,f178])).

fof(f178,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK9(X2,X3,sK3),k2_relat_1(sK3))
        | ~ r2_hidden(X2,k10_relat_1(sK3,X3)) )
    | ~ spl10_17 ),
    inference(resolution,[],[f175,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ sP7(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f175,plain,
    ( ! [X4,X5] :
        ( sP7(sK9(X4,X5,sK3),sK3)
        | ~ r2_hidden(X4,k10_relat_1(sK3,X5)) )
    | ~ spl10_17 ),
    inference(resolution,[],[f158,f31])).

% (16006)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (16024)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f31,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | sP7(X2,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK9(X0,X1,sK3)),sK3)
        | ~ r2_hidden(X0,k10_relat_1(sK3,X1)) )
    | ~ spl10_17 ),
    inference(resolution,[],[f144,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X0))
        | ~ r2_hidden(sK9(sK4,X0,sK3),k2_relat_1(sK3)) )
    | ~ spl10_11
    | ~ spl10_15
    | ~ spl10_17 ),
    inference(resolution,[],[f173,f108])).

fof(f108,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK2)
        | ~ r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl10_11 ),
    inference(resolution,[],[f105,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f105,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl10_11
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK4,X0,sK3),sK2)
        | ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) )
    | ~ spl10_15
    | ~ spl10_17 ),
    inference(resolution,[],[f158,f135])).

fof(f135,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(sK4,X5),sK3)
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2) )
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl10_15
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(k4_tarski(sK4,X5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f161,plain,
    ( ~ spl10_10
    | spl10_12
    | ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl10_10
    | spl10_12
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f159,f98])).

fof(f98,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl10_10
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f159,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl10_12
    | ~ spl10_16 ),
    inference(resolution,[],[f141,f112])).

fof(f112,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | spl10_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f141,plain,
    ( ! [X0] :
        ( r2_hidden(sK4,k10_relat_1(sK3,X0))
        | ~ r2_hidden(sK5,X0) )
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl10_16
  <=> ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | r2_hidden(sK4,k10_relat_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f157,plain,
    ( ~ spl10_5
    | spl10_17 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl10_5
    | spl10_17 ),
    inference(subsumption_resolution,[],[f155,f29])).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f155,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | ~ spl10_5
    | spl10_17 ),
    inference(resolution,[],[f151,f69])).

fof(f69,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl10_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl10_17 ),
    inference(resolution,[],[f145,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f145,plain,
    ( ~ v1_relat_1(sK3)
    | spl10_17 ),
    inference(avatar_component_clause,[],[f143])).

fof(f153,plain,
    ( ~ spl10_14
    | spl10_18 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl10_14
    | spl10_18 ),
    inference(subsumption_resolution,[],[f138,f149])).

fof(f149,plain,
    ( ~ r2_hidden(sK5,k2_relat_1(sK3))
    | spl10_18 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl10_18
  <=> r2_hidden(sK5,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f138,plain,
    ( r2_hidden(sK5,k2_relat_1(sK3))
    | ~ spl10_14 ),
    inference(resolution,[],[f131,f45])).

fof(f131,plain,
    ( sP7(sK5,sK3)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl10_14
  <=> sP7(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f150,plain,
    ( spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f126,f121,f147,f143,f140])).

fof(f121,plain,
    ( spl10_13
  <=> r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,k2_relat_1(sK3))
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(sK5,X0)
        | r2_hidden(sK4,k10_relat_1(sK3,X0)) )
    | ~ spl10_13 ),
    inference(resolution,[],[f123,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f123,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f136,plain,
    ( spl10_15
    | ~ spl10_12
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f115,f67,f111,f134])).

fof(f115,plain,
    ( ! [X5] :
        ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
        | ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl10_5 ),
    inference(forward_demodulation,[],[f19,f71])).

fof(f71,plain,
    ( ! [X0] : k8_relset_1(sK0,sK2,sK3,X0) = k10_relat_1(sK3,X0)
    | ~ spl10_5 ),
    inference(resolution,[],[f69,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f19,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <~> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X4,X5),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

fof(f132,plain,
    ( spl10_14
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f127,f121,f129])).

fof(f127,plain,
    ( sP7(sK5,sK3)
    | ~ spl10_13 ),
    inference(resolution,[],[f123,f31])).

fof(f124,plain,
    ( spl10_13
    | ~ spl10_5
    | spl10_12 ),
    inference(avatar_split_clause,[],[f119,f111,f67,f121])).

fof(f119,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ spl10_5
    | spl10_12 ),
    inference(subsumption_resolution,[],[f116,f112])).

fof(f116,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ spl10_5 ),
    inference(forward_demodulation,[],[f21,f71])).

fof(f21,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f114,plain,
    ( spl10_12
    | ~ spl10_5
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f109,f81,f67,f111])).

fof(f81,plain,
    ( spl10_7
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f109,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_5
    | ~ spl10_7 ),
    inference(superposition,[],[f83,f71])).

fof(f83,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f106,plain,
    ( spl10_11
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f101,f90,f76,f103])).

fof(f76,plain,
    ( spl10_6
  <=> m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f90,plain,
    ( spl10_9
  <=> k2_relset_1(sK0,sK2,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f101,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(superposition,[],[f78,f92])).

fof(f92,plain,
    ( k2_relset_1(sK0,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f90])).

fof(f78,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f99,plain,
    ( spl10_10
    | spl10_7 ),
    inference(avatar_split_clause,[],[f94,f81,f96])).

fof(f94,plain,
    ( r2_hidden(sK5,sK1)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f22,f82])).

fof(f82,plain,
    ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | spl10_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f22,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f93,plain,
    ( spl10_9
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f73,f67,f90])).

fof(f73,plain,
    ( k2_relset_1(sK0,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl10_5 ),
    inference(resolution,[],[f69,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f79,plain,
    ( spl10_6
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f72,f67,f76])).

fof(f72,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2))
    | ~ spl10_5 ),
    inference(resolution,[],[f69,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f70,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f24,f67])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:01:40 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (16007)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (16007)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f194,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f70,f79,f93,f99,f106,f114,f124,f132,f136,f150,f153,f157,f161,f193])).
% 0.21/0.47  fof(f193,plain,(
% 0.21/0.47    ~spl10_11 | ~spl10_12 | ~spl10_15 | ~spl10_17),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f192])).
% 0.21/0.47  fof(f192,plain,(
% 0.21/0.47    $false | (~spl10_11 | ~spl10_12 | ~spl10_15 | ~spl10_17)),
% 0.21/0.47    inference(subsumption_resolution,[],[f191,f144])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    v1_relat_1(sK3) | ~spl10_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f143])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    spl10_17 <=> v1_relat_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.21/0.47  fof(f191,plain,(
% 0.21/0.47    ~v1_relat_1(sK3) | (~spl10_11 | ~spl10_12 | ~spl10_15 | ~spl10_17)),
% 0.21/0.47    inference(subsumption_resolution,[],[f190,f113])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl10_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f111])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    spl10_12 <=> r2_hidden(sK4,k10_relat_1(sK3,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.21/0.47  fof(f190,plain,(
% 0.21/0.47    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | (~spl10_11 | ~spl10_15 | ~spl10_17)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f189])).
% 0.21/0.47  fof(f189,plain,(
% 0.21/0.47    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl10_11 | ~spl10_15 | ~spl10_17)),
% 0.21/0.47    inference(resolution,[],[f188,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) ) | (~spl10_11 | ~spl10_15 | ~spl10_17)),
% 0.21/0.47    inference(subsumption_resolution,[],[f179,f178])).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    ( ! [X2,X3] : (r2_hidden(sK9(X2,X3,sK3),k2_relat_1(sK3)) | ~r2_hidden(X2,k10_relat_1(sK3,X3))) ) | ~spl10_17),
% 0.21/0.47    inference(resolution,[],[f175,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X2,X0] : (~sP7(X2,X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.47    inference(equality_resolution,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~sP7(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    ( ! [X4,X5] : (sP7(sK9(X4,X5,sK3),sK3) | ~r2_hidden(X4,k10_relat_1(sK3,X5))) ) | ~spl10_17),
% 0.21/0.47    inference(resolution,[],[f158,f31])).
% 0.21/0.47  % (16006)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (16024)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | sP7(X2,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK9(X0,X1,sK3)),sK3) | ~r2_hidden(X0,k10_relat_1(sK3,X1))) ) | ~spl10_17),
% 0.21/0.47    inference(resolution,[],[f144,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f179,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X0)) | ~r2_hidden(sK9(sK4,X0,sK3),k2_relat_1(sK3))) ) | (~spl10_11 | ~spl10_15 | ~spl10_17)),
% 0.21/0.47    inference(resolution,[],[f173,f108])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(X0,sK2) | ~r2_hidden(X0,k2_relat_1(sK3))) ) | ~spl10_11),
% 0.21/0.47    inference(resolution,[],[f105,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | ~spl10_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    spl10_11 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.47  fof(f173,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK9(sK4,X0,sK3),sK2) | ~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) ) | (~spl10_15 | ~spl10_17)),
% 0.21/0.47    inference(resolution,[],[f158,f135])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    ( ! [X5] : (~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2)) ) | ~spl10_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f134])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    spl10_15 <=> ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    ~spl10_10 | spl10_12 | ~spl10_16),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f160])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    $false | (~spl10_10 | spl10_12 | ~spl10_16)),
% 0.21/0.47    inference(subsumption_resolution,[],[f159,f98])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    r2_hidden(sK5,sK1) | ~spl10_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f96])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl10_10 <=> r2_hidden(sK5,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    ~r2_hidden(sK5,sK1) | (spl10_12 | ~spl10_16)),
% 0.21/0.47    inference(resolution,[],[f141,f112])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | spl10_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f111])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK4,k10_relat_1(sK3,X0)) | ~r2_hidden(sK5,X0)) ) | ~spl10_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f140])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    spl10_16 <=> ! [X0] : (~r2_hidden(sK5,X0) | r2_hidden(sK4,k10_relat_1(sK3,X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    ~spl10_5 | spl10_17),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f156])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    $false | (~spl10_5 | spl10_17)),
% 0.21/0.47    inference(subsumption_resolution,[],[f155,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | (~spl10_5 | spl10_17)),
% 0.21/0.47    inference(resolution,[],[f151,f69])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl10_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f67])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl10_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl10_17),
% 0.21/0.47    inference(resolution,[],[f145,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    ~v1_relat_1(sK3) | spl10_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f143])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    ~spl10_14 | spl10_18),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f152])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    $false | (~spl10_14 | spl10_18)),
% 0.21/0.47    inference(subsumption_resolution,[],[f138,f149])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    ~r2_hidden(sK5,k2_relat_1(sK3)) | spl10_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f147])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    spl10_18 <=> r2_hidden(sK5,k2_relat_1(sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    r2_hidden(sK5,k2_relat_1(sK3)) | ~spl10_14),
% 0.21/0.47    inference(resolution,[],[f131,f45])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    sP7(sK5,sK3) | ~spl10_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f129])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    spl10_14 <=> sP7(sK5,sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f126,f121,f147,f143,f140])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    spl10_13 <=> r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK5,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~r2_hidden(sK5,X0) | r2_hidden(sK4,k10_relat_1(sK3,X0))) ) | ~spl10_13),
% 0.21/0.47    inference(resolution,[],[f123,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK4,sK5),sK3) | ~spl10_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f121])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    spl10_15 | ~spl10_12 | ~spl10_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f115,f67,f111,f134])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ( ! [X5] : (~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1)) ) | ~spl10_5),
% 0.21/0.47    inference(forward_demodulation,[],[f19,f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X0] : (k8_relset_1(sK0,sK2,sK3,X0) = k10_relat_1(sK3,X0)) ) | ~spl10_5),
% 0.21/0.47    inference(resolution,[],[f69,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f9])).
% 0.21/0.47  fof(f9,conjecture,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    spl10_14 | ~spl10_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f127,f121,f129])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    sP7(sK5,sK3) | ~spl10_13),
% 0.21/0.47    inference(resolution,[],[f123,f31])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    spl10_13 | ~spl10_5 | spl10_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f119,f111,f67,f121])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK4,sK5),sK3) | (~spl10_5 | spl10_12)),
% 0.21/0.47    inference(subsumption_resolution,[],[f116,f112])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | r2_hidden(k4_tarski(sK4,sK5),sK3) | ~spl10_5),
% 0.21/0.47    inference(forward_demodulation,[],[f21,f71])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl10_12 | ~spl10_5 | ~spl10_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f109,f81,f67,f111])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl10_7 <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl10_5 | ~spl10_7)),
% 0.21/0.47    inference(superposition,[],[f83,f71])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | ~spl10_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f81])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    spl10_11 | ~spl10_6 | ~spl10_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f101,f90,f76,f103])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl10_6 <=> m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl10_9 <=> k2_relset_1(sK0,sK2,sK3) = k2_relat_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | (~spl10_6 | ~spl10_9)),
% 0.21/0.47    inference(superposition,[],[f78,f92])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    k2_relset_1(sK0,sK2,sK3) = k2_relat_1(sK3) | ~spl10_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f90])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2)) | ~spl10_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f76])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    spl10_10 | spl10_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f94,f81,f96])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    r2_hidden(sK5,sK1) | spl10_7),
% 0.21/0.47    inference(subsumption_resolution,[],[f22,f82])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | spl10_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f81])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    r2_hidden(sK5,sK1) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    spl10_9 | ~spl10_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f73,f67,f90])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    k2_relset_1(sK0,sK2,sK3) = k2_relat_1(sK3) | ~spl10_5),
% 0.21/0.47    inference(resolution,[],[f69,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(X2) = k2_relset_1(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl10_6 | ~spl10_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f72,f67,f76])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2)) | ~spl10_5),
% 0.21/0.47    inference(resolution,[],[f69,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    spl10_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f67])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (16007)------------------------------
% 0.21/0.47  % (16007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (16007)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (16007)Memory used [KB]: 10746
% 0.21/0.47  % (16007)Time elapsed: 0.056 s
% 0.21/0.47  % (16007)------------------------------
% 0.21/0.47  % (16007)------------------------------
% 0.21/0.48  % (16002)Success in time 0.116 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 188 expanded)
%              Number of leaves         :   25 (  78 expanded)
%              Depth                    :    8
%              Number of atoms          :  305 ( 547 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f252,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f65,f77,f82,f87,f104,f112,f116,f124,f168,f181,f192,f216,f229,f244,f251])).

fof(f251,plain,
    ( spl10_25
    | ~ spl10_29 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl10_25
    | ~ spl10_29 ),
    inference(subsumption_resolution,[],[f249,f228])).

fof(f228,plain,
    ( ~ m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | spl10_25 ),
    inference(avatar_component_clause,[],[f227])).

% (9467)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f227,plain,
    ( spl10_25
  <=> m1_subset_1(sK6(sK4,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f249,plain,
    ( m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_29 ),
    inference(resolution,[],[f243,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f243,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl10_29
  <=> r2_hidden(sK6(sK4,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f244,plain,
    ( spl10_29
    | ~ spl10_12
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f217,f179,f114,f242])).

fof(f114,plain,
    ( spl10_12
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f179,plain,
    ( spl10_22
  <=> r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f217,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_12
    | ~ spl10_22 ),
    inference(resolution,[],[f140,f180])).

fof(f180,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3))
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f179])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(X0,sK2) )
    | ~ spl10_12 ),
    inference(resolution,[],[f115,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f115,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f114])).

fof(f229,plain,
    ( ~ spl10_25
    | ~ spl10_11
    | ~ spl10_19
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f223,f214,f166,f110,f227])).

fof(f110,plain,
    ( spl10_11
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(k4_tarski(sK4,X5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f166,plain,
    ( spl10_19
  <=> r2_hidden(sK6(sK4,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f214,plain,
    ( spl10_24
  <=> r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f223,plain,
    ( ~ m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_11
    | ~ spl10_19
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f218,f167])).

fof(f167,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK1)
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f166])).

fof(f218,plain,
    ( ~ r2_hidden(sK6(sK4,sK1,sK3),sK1)
    | ~ m1_subset_1(sK6(sK4,sK1,sK3),sK2)
    | ~ spl10_11
    | ~ spl10_24 ),
    inference(resolution,[],[f215,f111])).

fof(f111,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(sK4,X5),sK3)
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2) )
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f215,plain,
    ( r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3)
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f214])).

fof(f216,plain,
    ( spl10_24
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f200,f85,f63,f214])).

fof(f63,plain,
    ( spl10_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f85,plain,
    ( spl10_8
  <=> r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f200,plain,
    ( r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3)
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f197,f64])).

fof(f64,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f197,plain,
    ( r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_8 ),
    inference(resolution,[],[f86,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f86,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f192,plain,
    ( spl10_9
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f191,f102,f80,f98])).

fof(f98,plain,
    ( spl10_9
  <=> sP8(sK4,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f80,plain,
    ( spl10_7
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f102,plain,
    ( spl10_10
  <=> r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f191,plain,
    ( sP8(sK4,sK1,sK3)
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(resolution,[],[f184,f81])).

fof(f81,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | sP8(sK4,X0,sK3) )
    | ~ spl10_10 ),
    inference(resolution,[],[f103,f32])).

fof(f32,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f103,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f181,plain,
    ( spl10_22
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f155,f85,f63,f179])).

fof(f155,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3))
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f151,f64])).

fof(f151,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl10_8 ),
    inference(resolution,[],[f86,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f168,plain,
    ( spl10_19
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f157,f85,f63,f166])).

fof(f157,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK1)
    | ~ spl10_3
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f153,f64])).

fof(f153,plain,
    ( r2_hidden(sK6(sK4,sK1,sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl10_8 ),
    inference(resolution,[],[f86,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f124,plain,
    ( ~ spl10_2
    | ~ spl10_3
    | spl10_4
    | ~ spl10_9 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_3
    | spl10_4
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f122,f121])).

fof(f121,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_3
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f107,f64])).

fof(f107,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_9 ),
    inference(resolution,[],[f99,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP8(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f99,plain,
    ( sP8(sK4,sK1,sK3)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f122,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_2
    | spl10_4 ),
    inference(forward_demodulation,[],[f108,f58])).

fof(f58,plain,
    ( ! [X0] : k8_relset_1(sK0,sK2,sK3,X0) = k10_relat_1(sK3,X0)
    | ~ spl10_2 ),
    inference(resolution,[],[f54,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f54,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl10_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f108,plain,
    ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | spl10_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl10_4
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f116,plain,
    ( spl10_12
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f78,f75,f53,f114])).

fof(f75,plain,
    ( spl10_6
  <=> m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f78,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(forward_demodulation,[],[f76,f57])).

fof(f57,plain,
    ( k2_relset_1(sK0,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl10_2 ),
    inference(resolution,[],[f54,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f76,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f112,plain,
    ( ~ spl10_4
    | spl10_11 ),
    inference(avatar_split_clause,[],[f22,f110,f67])).

fof(f22,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f104,plain,
    ( spl10_4
    | spl10_10 ),
    inference(avatar_split_clause,[],[f24,f102,f67])).

fof(f24,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f87,plain,
    ( spl10_8
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f83,f67,f53,f85])).

fof(f83,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f68,f58])).

fof(f68,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f82,plain,
    ( spl10_4
    | spl10_7 ),
    inference(avatar_split_clause,[],[f25,f80,f67])).

fof(f25,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f77,plain,
    ( spl10_6
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f56,f53,f75])).

fof(f56,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2))
    | ~ spl10_2 ),
    inference(resolution,[],[f54,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f65,plain,
    ( spl10_3
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f61,f53,f63])).

fof(f61,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f59,f43])).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f59,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK3)
    | ~ spl10_2 ),
    inference(resolution,[],[f54,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f55,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f27,f53])).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:56:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (9450)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (9463)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (9456)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (9469)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (9455)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (9454)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (9453)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (9449)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (9462)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (9449)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f252,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f55,f65,f77,f82,f87,f104,f112,f116,f124,f168,f181,f192,f216,f229,f244,f251])).
% 0.22/0.51  fof(f251,plain,(
% 0.22/0.51    spl10_25 | ~spl10_29),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f250])).
% 0.22/0.51  fof(f250,plain,(
% 0.22/0.51    $false | (spl10_25 | ~spl10_29)),
% 0.22/0.51    inference(subsumption_resolution,[],[f249,f228])).
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    ~m1_subset_1(sK6(sK4,sK1,sK3),sK2) | spl10_25),
% 0.22/0.51    inference(avatar_component_clause,[],[f227])).
% 0.22/0.51  % (9467)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  fof(f227,plain,(
% 0.22/0.51    spl10_25 <=> m1_subset_1(sK6(sK4,sK1,sK3),sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 0.22/0.51  fof(f249,plain,(
% 0.22/0.51    m1_subset_1(sK6(sK4,sK1,sK3),sK2) | ~spl10_29),
% 0.22/0.51    inference(resolution,[],[f243,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    r2_hidden(sK6(sK4,sK1,sK3),sK2) | ~spl10_29),
% 0.22/0.51    inference(avatar_component_clause,[],[f242])).
% 0.22/0.51  fof(f242,plain,(
% 0.22/0.51    spl10_29 <=> r2_hidden(sK6(sK4,sK1,sK3),sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 0.22/0.51  fof(f244,plain,(
% 0.22/0.51    spl10_29 | ~spl10_12 | ~spl10_22),
% 0.22/0.51    inference(avatar_split_clause,[],[f217,f179,f114,f242])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    spl10_12 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    spl10_22 <=> r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.22/0.51  fof(f217,plain,(
% 0.22/0.51    r2_hidden(sK6(sK4,sK1,sK3),sK2) | (~spl10_12 | ~spl10_22)),
% 0.22/0.51    inference(resolution,[],[f140,f180])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3)) | ~spl10_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f179])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(X0,sK2)) ) | ~spl10_12),
% 0.22/0.51    inference(resolution,[],[f115,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | ~spl10_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f114])).
% 0.22/0.51  fof(f229,plain,(
% 0.22/0.51    ~spl10_25 | ~spl10_11 | ~spl10_19 | ~spl10_24),
% 0.22/0.51    inference(avatar_split_clause,[],[f223,f214,f166,f110,f227])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    spl10_11 <=> ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    spl10_19 <=> r2_hidden(sK6(sK4,sK1,sK3),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.22/0.51  fof(f214,plain,(
% 0.22/0.51    spl10_24 <=> r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    ~m1_subset_1(sK6(sK4,sK1,sK3),sK2) | (~spl10_11 | ~spl10_19 | ~spl10_24)),
% 0.22/0.51    inference(subsumption_resolution,[],[f218,f167])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    r2_hidden(sK6(sK4,sK1,sK3),sK1) | ~spl10_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f166])).
% 0.22/0.51  fof(f218,plain,(
% 0.22/0.51    ~r2_hidden(sK6(sK4,sK1,sK3),sK1) | ~m1_subset_1(sK6(sK4,sK1,sK3),sK2) | (~spl10_11 | ~spl10_24)),
% 0.22/0.51    inference(resolution,[],[f215,f111])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    ( ! [X5] : (~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2)) ) | ~spl10_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f110])).
% 0.22/0.51  fof(f215,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3) | ~spl10_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f214])).
% 0.22/0.51  fof(f216,plain,(
% 0.22/0.51    spl10_24 | ~spl10_3 | ~spl10_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f200,f85,f63,f214])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    spl10_3 <=> v1_relat_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl10_8 <=> r2_hidden(sK4,k10_relat_1(sK3,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3) | (~spl10_3 | ~spl10_8)),
% 0.22/0.51    inference(subsumption_resolution,[],[f197,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    v1_relat_1(sK3) | ~spl10_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f63])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK4,sK6(sK4,sK1,sK3)),sK3) | ~v1_relat_1(sK3) | ~spl10_8),
% 0.22/0.51    inference(resolution,[],[f86,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) | ~v1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl10_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f85])).
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    spl10_9 | ~spl10_7 | ~spl10_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f191,f102,f80,f98])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    spl10_9 <=> sP8(sK4,sK1,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    spl10_7 <=> r2_hidden(sK5,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    spl10_10 <=> r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    sP8(sK4,sK1,sK3) | (~spl10_7 | ~spl10_10)),
% 0.22/0.51    inference(resolution,[],[f184,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    r2_hidden(sK5,sK1) | ~spl10_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f80])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(sK5,X0) | sP8(sK4,X0,sK3)) ) | ~spl10_10),
% 0.22/0.51    inference(resolution,[],[f103,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | sP8(X3,X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK4,sK5),sK3) | ~spl10_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f102])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    spl10_22 | ~spl10_3 | ~spl10_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f155,f85,f63,f179])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3)) | (~spl10_3 | ~spl10_8)),
% 0.22/0.51    inference(subsumption_resolution,[],[f151,f64])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    r2_hidden(sK6(sK4,sK1,sK3),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl10_8),
% 0.22/0.51    inference(resolution,[],[f86,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    spl10_19 | ~spl10_3 | ~spl10_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f157,f85,f63,f166])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    r2_hidden(sK6(sK4,sK1,sK3),sK1) | (~spl10_3 | ~spl10_8)),
% 0.22/0.51    inference(subsumption_resolution,[],[f153,f64])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    r2_hidden(sK6(sK4,sK1,sK3),sK1) | ~v1_relat_1(sK3) | ~spl10_8),
% 0.22/0.51    inference(resolution,[],[f86,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    ~spl10_2 | ~spl10_3 | spl10_4 | ~spl10_9),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f123])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    $false | (~spl10_2 | ~spl10_3 | spl10_4 | ~spl10_9)),
% 0.22/0.51    inference(subsumption_resolution,[],[f122,f121])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl10_3 | ~spl10_9)),
% 0.22/0.51    inference(subsumption_resolution,[],[f107,f64])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    ~v1_relat_1(sK3) | r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl10_9),
% 0.22/0.51    inference(resolution,[],[f99,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (~sP8(X3,X1,X0) | ~v1_relat_1(X0) | r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.22/0.51    inference(equality_resolution,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~sP8(X3,X1,X0) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    sP8(sK4,sK1,sK3) | ~spl10_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f98])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl10_2 | spl10_4)),
% 0.22/0.51    inference(forward_demodulation,[],[f108,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X0] : (k8_relset_1(sK0,sK2,sK3,X0) = k10_relat_1(sK3,X0)) ) | ~spl10_2),
% 0.22/0.51    inference(resolution,[],[f54,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl10_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    spl10_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | spl10_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    spl10_4 <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    spl10_12 | ~spl10_2 | ~spl10_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f78,f75,f53,f114])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    spl10_6 <=> m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | (~spl10_2 | ~spl10_6)),
% 0.22/0.51    inference(forward_demodulation,[],[f76,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    k2_relset_1(sK0,sK2,sK3) = k2_relat_1(sK3) | ~spl10_2),
% 0.22/0.51    inference(resolution,[],[f54,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(X2) = k2_relset_1(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2)) | ~spl10_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f75])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    ~spl10_4 | spl10_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f22,f110,f67])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)))))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.51  fof(f11,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f10])).
% 0.22/0.51  fof(f10,conjecture,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    spl10_4 | spl10_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f24,f102,f67])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    spl10_8 | ~spl10_2 | ~spl10_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f83,f67,f53,f85])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | (~spl10_2 | ~spl10_4)),
% 0.22/0.51    inference(forward_demodulation,[],[f68,f58])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | ~spl10_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f67])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    spl10_4 | spl10_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f25,f80,f67])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    r2_hidden(sK5,sK1) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    spl10_6 | ~spl10_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f56,f53,f75])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    m1_subset_1(k2_relset_1(sK0,sK2,sK3),k1_zfmisc_1(sK2)) | ~spl10_2),
% 0.22/0.51    inference(resolution,[],[f54,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    spl10_3 | ~spl10_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f61,f53,f63])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    v1_relat_1(sK3) | ~spl10_2),
% 0.22/0.51    inference(subsumption_resolution,[],[f59,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | v1_relat_1(sK3) | ~spl10_2),
% 0.22/0.51    inference(resolution,[],[f54,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    spl10_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f27,f53])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (9449)------------------------------
% 0.22/0.51  % (9449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9449)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (9449)Memory used [KB]: 6268
% 0.22/0.51  % (9449)Time elapsed: 0.094 s
% 0.22/0.51  % (9449)------------------------------
% 0.22/0.51  % (9449)------------------------------
% 0.22/0.51  % (9466)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (9448)Success in time 0.149 s
%------------------------------------------------------------------------------

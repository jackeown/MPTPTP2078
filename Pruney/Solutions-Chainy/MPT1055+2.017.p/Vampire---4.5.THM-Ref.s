%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 243 expanded)
%              Number of leaves         :   32 (  88 expanded)
%              Depth                    :   10
%              Number of atoms          :  442 ( 790 expanded)
%              Number of equality atoms :   41 (  52 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f351,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f100,f105,f111,f121,f133,f140,f157,f167,f179,f188,f202,f221,f297,f303,f310,f339,f343,f350])).

fof(f350,plain,
    ( ~ spl6_7
    | ~ spl6_8
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_8
    | spl6_10 ),
    inference(subsumption_resolution,[],[f344,f132])).

fof(f132,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_10
  <=> r1_tarski(k9_relat_1(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f344,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f299,f110])).

fof(f110,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f299,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_8 ),
    inference(superposition,[],[f116,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f116,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_8
  <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f343,plain,
    ( ~ spl6_5
    | spl6_30 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | ~ spl6_5
    | spl6_30 ),
    inference(subsumption_resolution,[],[f341,f99])).

fof(f99,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f341,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | spl6_30 ),
    inference(resolution,[],[f338,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f338,plain,
    ( ~ r1_tarski(sK3,sK0)
    | spl6_30 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl6_30
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f339,plain,
    ( ~ spl6_30
    | ~ spl6_1
    | ~ spl6_10
    | spl6_11
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f315,f185,f154,f137,f130,f73,f336])).

fof(f73,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f137,plain,
    ( spl6_11
  <=> r1_tarski(sK3,k10_relat_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f154,plain,
    ( spl6_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f185,plain,
    ( spl6_18
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f315,plain,
    ( ~ r1_tarski(sK3,sK0)
    | ~ spl6_1
    | ~ spl6_10
    | spl6_11
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f312,f131])).

fof(f131,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f312,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ r1_tarski(sK3,sK0)
    | ~ spl6_1
    | spl6_11
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(resolution,[],[f138,f225])).

fof(f225,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k10_relat_1(sK2,X1))
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f222,f155])).

fof(f155,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f154])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK0)
        | ~ v1_relat_1(sK2)
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | r1_tarski(X0,k10_relat_1(sK2,X1)) )
    | ~ spl6_1
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f87,f187])).

fof(f187,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f185])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2)
        | ~ r1_tarski(X0,k1_relat_1(sK2))
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | r1_tarski(X0,k10_relat_1(sK2,X1)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f75,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f75,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f138,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f310,plain,
    ( ~ spl6_7
    | spl6_9
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl6_7
    | spl6_9
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f308,f110])).

fof(f308,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_9
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f307,f139])).

fof(f139,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f307,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_9 ),
    inference(superposition,[],[f119,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f119,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_9
  <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f303,plain,
    ( ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f298,f116])).

fof(f298,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f38,f120])).

fof(f120,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f38,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).

fof(f297,plain,
    ( spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f293,f139])).

fof(f293,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | spl6_10
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(resolution,[],[f243,f152])).

fof(f152,plain,
    ( ! [X2] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl6_13
  <=> ! [X2] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,X0),sK4)
        | ~ r1_tarski(sK3,X0) )
    | spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f239,f155])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,X0),sK4)
        | ~ r1_tarski(sK3,X0)
        | ~ v1_relat_1(sK2) )
    | spl6_10 ),
    inference(resolution,[],[f134,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,sK3),X0)
        | ~ r1_tarski(X0,sK4) )
    | spl6_10 ),
    inference(resolution,[],[f132,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f221,plain,
    ( ~ spl6_7
    | spl6_14 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl6_7
    | spl6_14 ),
    inference(subsumption_resolution,[],[f218,f49])).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f218,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_7
    | spl6_14 ),
    inference(resolution,[],[f158,f110])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_14 ),
    inference(resolution,[],[f156,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f156,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f154])).

fof(f202,plain,
    ( spl6_15
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | spl6_15
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f199,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f199,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5(k1_xboole_0))
    | spl6_15
    | ~ spl6_17 ),
    inference(superposition,[],[f166,f178])).

fof(f178,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl6_17
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f166,plain,
    ( ~ r1_tarski(sK1,sK5(sK1))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl6_15
  <=> r1_tarski(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f188,plain,
    ( spl6_18
    | ~ spl6_7
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f182,f172,f108,f185])).

fof(f172,plain,
    ( spl6_16
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f182,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_7
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f180,f110])).

fof(f180,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_16 ),
    inference(superposition,[],[f174,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f174,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f172])).

fof(f179,plain,
    ( spl6_16
    | spl6_17
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f168,f108,f102,f176,f172])).

fof(f102,plain,
    ( spl6_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f168,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f106,f110])).

fof(f106,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_6 ),
    inference(resolution,[],[f104,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f104,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f167,plain,
    ( ~ spl6_15
    | spl6_2 ),
    inference(avatar_split_clause,[],[f146,f78,f164])).

fof(f78,plain,
    ( spl6_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f146,plain,
    ( ~ r1_tarski(sK1,sK5(sK1))
    | spl6_2 ),
    inference(resolution,[],[f112,f48])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f112,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ r1_tarski(sK1,X0) )
    | spl6_2 ),
    inference(resolution,[],[f89,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f89,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,sK1) )
    | spl6_2 ),
    inference(resolution,[],[f80,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f80,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f157,plain,
    ( spl6_13
    | ~ spl6_14
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f88,f73,f154,f151])).

fof(f88,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(sK2)
        | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2) )
    | ~ spl6_1 ),
    inference(resolution,[],[f75,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f140,plain,
    ( spl6_11
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f128,f118,f108,f137])).

fof(f128,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f127,f110])).

fof(f127,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_9 ),
    inference(superposition,[],[f120,f65])).

fof(f133,plain,
    ( ~ spl6_10
    | ~ spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f126,f114,f108,f130])).

fof(f126,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_7
    | spl6_8 ),
    inference(subsumption_resolution,[],[f125,f110])).

fof(f125,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_8 ),
    inference(superposition,[],[f115,f66])).

fof(f115,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f121,plain,
    ( spl6_8
    | spl6_9 ),
    inference(avatar_split_clause,[],[f37,f118,f114])).

fof(f37,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f111,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f43,f108])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f105,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f42,f102])).

fof(f42,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f100,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f40,f97])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f44,f78])).

fof(f44,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f41,f73])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:32:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (12271)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (12266)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (12264)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (12266)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f351,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f76,f81,f100,f105,f111,f121,f133,f140,f157,f167,f179,f188,f202,f221,f297,f303,f310,f339,f343,f350])).
% 0.21/0.49  fof(f350,plain,(
% 0.21/0.49    ~spl6_7 | ~spl6_8 | spl6_10),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f349])).
% 0.21/0.49  fof(f349,plain,(
% 0.21/0.49    $false | (~spl6_7 | ~spl6_8 | spl6_10)),
% 0.21/0.49    inference(subsumption_resolution,[],[f344,f132])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | spl6_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    spl6_10 <=> r1_tarski(k9_relat_1(sK2,sK3),sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.49  fof(f344,plain,(
% 0.21/0.49    r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl6_7 | ~spl6_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f299,f110])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f108])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl6_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_8),
% 0.21/0.49    inference(superposition,[],[f116,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl6_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl6_8 <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.49  fof(f343,plain,(
% 0.21/0.49    ~spl6_5 | spl6_30),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f342])).
% 0.21/0.49  fof(f342,plain,(
% 0.21/0.49    $false | (~spl6_5 | spl6_30)),
% 0.21/0.49    inference(subsumption_resolution,[],[f341,f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl6_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl6_5 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.49  fof(f341,plain,(
% 0.21/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | spl6_30),
% 0.21/0.49    inference(resolution,[],[f338,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f338,plain,(
% 0.21/0.49    ~r1_tarski(sK3,sK0) | spl6_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f336])).
% 0.21/0.49  fof(f336,plain,(
% 0.21/0.49    spl6_30 <=> r1_tarski(sK3,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.49  fof(f339,plain,(
% 0.21/0.49    ~spl6_30 | ~spl6_1 | ~spl6_10 | spl6_11 | ~spl6_14 | ~spl6_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f315,f185,f154,f137,f130,f73,f336])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl6_1 <=> v1_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl6_11 <=> r1_tarski(sK3,k10_relat_1(sK2,sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    spl6_14 <=> v1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    spl6_18 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    ~r1_tarski(sK3,sK0) | (~spl6_1 | ~spl6_10 | spl6_11 | ~spl6_14 | ~spl6_18)),
% 0.21/0.49    inference(subsumption_resolution,[],[f312,f131])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~spl6_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f130])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~r1_tarski(sK3,sK0) | (~spl6_1 | spl6_11 | ~spl6_14 | ~spl6_18)),
% 0.21/0.49    inference(resolution,[],[f138,f225])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(sK2,X1)) | ~r1_tarski(k9_relat_1(sK2,X0),X1) | ~r1_tarski(X0,sK0)) ) | (~spl6_1 | ~spl6_14 | ~spl6_18)),
% 0.21/0.49    inference(subsumption_resolution,[],[f222,f155])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    v1_relat_1(sK2) | ~spl6_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f154])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,sK0) | ~v1_relat_1(sK2) | ~r1_tarski(k9_relat_1(sK2,X0),X1) | r1_tarski(X0,k10_relat_1(sK2,X1))) ) | (~spl6_1 | ~spl6_18)),
% 0.21/0.49    inference(forward_demodulation,[],[f87,f187])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK2) | ~spl6_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f185])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(sK2) | ~r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(k9_relat_1(sK2,X0),X1) | r1_tarski(X0,k10_relat_1(sK2,X1))) ) | ~spl6_1),
% 0.21/0.49    inference(resolution,[],[f75,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    v1_funct_1(sK2) | ~spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f73])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | spl6_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f137])).
% 0.21/0.49  fof(f310,plain,(
% 0.21/0.49    ~spl6_7 | spl6_9 | ~spl6_11),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f309])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    $false | (~spl6_7 | spl6_9 | ~spl6_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f308,f110])).
% 0.21/0.49  fof(f308,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl6_9 | ~spl6_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f307,f139])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~spl6_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f137])).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_9),
% 0.21/0.49    inference(superposition,[],[f119,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | spl6_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f118])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    spl6_9 <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.49  fof(f303,plain,(
% 0.21/0.49    ~spl6_8 | ~spl6_9),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f302])).
% 0.21/0.49  fof(f302,plain,(
% 0.21/0.49    $false | (~spl6_8 | ~spl6_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f298,f116])).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl6_9),
% 0.21/0.49    inference(subsumption_resolution,[],[f38,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~spl6_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f118])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f16])).
% 0.21/0.49  fof(f16,conjecture,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).
% 0.21/0.49  fof(f297,plain,(
% 0.21/0.49    spl6_10 | ~spl6_11 | ~spl6_13 | ~spl6_14),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f296])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    $false | (spl6_10 | ~spl6_11 | ~spl6_13 | ~spl6_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f293,f139])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (spl6_10 | ~spl6_13 | ~spl6_14)),
% 0.21/0.49    inference(resolution,[],[f243,f152])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ( ! [X2] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2)) ) | ~spl6_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f151])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    spl6_13 <=> ! [X2] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,X0),sK4) | ~r1_tarski(sK3,X0)) ) | (spl6_10 | ~spl6_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f239,f155])).
% 0.21/0.49  fof(f239,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,X0),sK4) | ~r1_tarski(sK3,X0) | ~v1_relat_1(sK2)) ) | spl6_10),
% 0.21/0.49    inference(resolution,[],[f134,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,sK3),X0) | ~r1_tarski(X0,sK4)) ) | spl6_10),
% 0.21/0.49    inference(resolution,[],[f132,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ~spl6_7 | spl6_14),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f220])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    $false | (~spl6_7 | spl6_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f218,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl6_7 | spl6_14)),
% 0.21/0.49    inference(resolution,[],[f158,f110])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_14),
% 0.21/0.49    inference(resolution,[],[f156,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | spl6_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f154])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    spl6_15 | ~spl6_17),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f201])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    $false | (spl6_15 | ~spl6_17)),
% 0.21/0.49    inference(subsumption_resolution,[],[f199,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    ~r1_tarski(k1_xboole_0,sK5(k1_xboole_0)) | (spl6_15 | ~spl6_17)),
% 0.21/0.49    inference(superposition,[],[f166,f178])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl6_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f176])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    spl6_17 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    ~r1_tarski(sK1,sK5(sK1)) | spl6_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f164])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    spl6_15 <=> r1_tarski(sK1,sK5(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    spl6_18 | ~spl6_7 | ~spl6_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f182,f172,f108,f185])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    spl6_16 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK2) | (~spl6_7 | ~spl6_16)),
% 0.21/0.49    inference(subsumption_resolution,[],[f180,f110])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_16),
% 0.21/0.49    inference(superposition,[],[f174,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl6_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f172])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    spl6_16 | spl6_17 | ~spl6_6 | ~spl6_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f168,f108,f102,f176,f172])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl6_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl6_6 | ~spl6_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f106,f110])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_6),
% 0.21/0.49    inference(resolution,[],[f104,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK1) | ~spl6_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f102])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ~spl6_15 | spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f146,f78,f164])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl6_2 <=> v1_xboole_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    ~r1_tarski(sK1,sK5(sK1)) | spl6_2),
% 0.21/0.49    inference(resolution,[],[f112,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(sK5(X0),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~r1_tarski(sK1,X0)) ) | spl6_2),
% 0.21/0.49    inference(resolution,[],[f89,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,sK1)) ) | spl6_2),
% 0.21/0.49    inference(resolution,[],[f80,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ~v1_xboole_0(sK1) | spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f78])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    spl6_13 | ~spl6_14 | ~spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f88,f73,f154,f151])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X2] : (~v1_relat_1(sK2) | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2)) ) | ~spl6_1),
% 0.21/0.49    inference(resolution,[],[f75,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl6_11 | ~spl6_7 | ~spl6_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f128,f118,f108,f137])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl6_7 | ~spl6_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f127,f110])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_9),
% 0.21/0.49    inference(superposition,[],[f120,f65])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ~spl6_10 | ~spl6_7 | spl6_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f126,f114,f108,f130])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl6_7 | spl6_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f125,f110])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_8),
% 0.21/0.49    inference(superposition,[],[f115,f66])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | spl6_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f114])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    spl6_8 | spl6_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f118,f114])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    spl6_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f43,f108])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f102])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl6_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f40,f97])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ~spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f44,f78])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ~v1_xboole_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f41,f73])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (12266)------------------------------
% 0.21/0.49  % (12266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12266)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (12266)Memory used [KB]: 10746
% 0.21/0.49  % (12266)Time elapsed: 0.074 s
% 0.21/0.49  % (12266)------------------------------
% 0.21/0.49  % (12266)------------------------------
% 0.21/0.49  % (12262)Success in time 0.126 s
%------------------------------------------------------------------------------

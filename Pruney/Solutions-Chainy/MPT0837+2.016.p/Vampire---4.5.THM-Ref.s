%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 147 expanded)
%              Number of leaves         :   20 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  260 ( 390 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f79,f84,f92,f116,f126,f133,f140,f148,f152,f156,f159])).

fof(f159,plain,
    ( ~ spl9_3
    | spl9_4
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl9_3
    | spl9_4
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f157,f91])).

fof(f91,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl9_8
  <=> r2_hidden(sK3,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f157,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f153,f60])).

fof(f60,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl9_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f153,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl9_4 ),
    inference(superposition,[],[f65,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f65,plain,
    ( ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | spl9_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl9_4
  <=> r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f156,plain,
    ( ~ spl9_7
    | spl9_9 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | ~ spl9_7
    | spl9_9 ),
    inference(subsumption_resolution,[],[f149,f99])).

fof(f99,plain,
    ( ~ sP6(sK3,sK2)
    | spl9_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl9_9
  <=> sP6(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f149,plain,
    ( sP6(sK3,sK2)
    | ~ spl9_7 ),
    inference(resolution,[],[f83,f33])).

fof(f33,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f83,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl9_7
  <=> r2_hidden(k4_tarski(sK4,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f152,plain,
    ( spl9_8
    | ~ spl9_9 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl9_8
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f150,f98])).

fof(f98,plain,
    ( sP6(sK3,sK2)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f150,plain,
    ( ~ sP6(sK3,sK2)
    | spl9_8 ),
    inference(resolution,[],[f90,f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ sP6(X2,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f90,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | spl9_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f148,plain,
    ( ~ spl9_8
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f146,f91])).

fof(f146,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(forward_demodulation,[],[f143,f139])).

fof(f139,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK1)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl9_15
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f143,plain,
    ( ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ spl9_11
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f142,f111])).

fof(f111,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl9_11
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f142,plain,
    ( ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl9_12 ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,
    ( ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ spl9_12 ),
    inference(resolution,[],[f128,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f128,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK8(sK3,X0,sK2),sK1)
        | ~ r2_hidden(sK3,k9_relat_1(sK2,X0)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f115,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f115,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK8(sK3,X0,sK2),sK1)
        | ~ r2_hidden(sK3,k9_relat_1(sK2,X0)) )
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl9_12
  <=> ! [X0] :
        ( ~ m1_subset_1(sK8(sK3,X0,sK2),sK1)
        | ~ r2_hidden(sK3,k9_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f140,plain,
    ( spl9_15
    | ~ spl9_11
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f135,f130,f110,f137])).

fof(f130,plain,
    ( spl9_14
  <=> sK2 = k7_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f135,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK1)
    | ~ spl9_11
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f134,f111])).

fof(f134,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl9_14 ),
    inference(superposition,[],[f29,f132])).

fof(f132,plain,
    ( sK2 = k7_relat_1(sK2,sK1)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f130])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f133,plain,
    ( spl9_14
    | ~ spl9_6
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f127,f110,f76,f130])).

fof(f76,plain,
    ( spl9_6
  <=> v4_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f127,plain,
    ( sK2 = k7_relat_1(sK2,sK1)
    | ~ spl9_6
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f85,f111])).

fof(f85,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k7_relat_1(sK2,sK1)
    | ~ spl9_6 ),
    inference(resolution,[],[f78,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f78,plain,
    ( v4_relat_1(sK2,sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f126,plain,
    ( ~ spl9_3
    | spl9_11 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | ~ spl9_3
    | spl9_11 ),
    inference(subsumption_resolution,[],[f123,f28])).

fof(f28,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f123,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl9_3
    | spl9_11 ),
    inference(resolution,[],[f117,f60])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl9_11 ),
    inference(resolution,[],[f112,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f112,plain,
    ( ~ v1_relat_1(sK2)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f116,plain,
    ( ~ spl9_11
    | spl9_12
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f95,f64,f114,f110])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK8(sK3,X0,sK2),sK1)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(sK3,k9_relat_1(sK2,X0)) )
    | ~ spl9_4 ),
    inference(resolution,[],[f93,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f93,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f21,f66])).

fof(f66,plain,
    ( r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f21,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f92,plain,
    ( spl9_8
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f87,f64,f58,f89])).

fof(f87,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f86,f60])).

fof(f86,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl9_4 ),
    inference(superposition,[],[f66,f42])).

fof(f84,plain,
    ( spl9_7
    | spl9_4 ),
    inference(avatar_split_clause,[],[f74,f64,f81])).

fof(f74,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | spl9_4 ),
    inference(subsumption_resolution,[],[f23,f65])).

fof(f23,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f79,plain,
    ( spl9_6
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f62,f58,f76])).

fof(f62,plain,
    ( v4_relat_1(sK2,sK1)
    | ~ spl9_3 ),
    inference(resolution,[],[f60,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f61,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f24,f58])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:21:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (6792)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (6800)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.46  % (6800)Refutation not found, incomplete strategy% (6800)------------------------------
% 0.21/0.46  % (6800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (6800)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (6800)Memory used [KB]: 1663
% 0.21/0.46  % (6800)Time elapsed: 0.056 s
% 0.21/0.46  % (6800)------------------------------
% 0.21/0.46  % (6800)------------------------------
% 0.21/0.47  % (6790)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (6790)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f61,f79,f84,f92,f116,f126,f133,f140,f148,f152,f156,f159])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    ~spl9_3 | spl9_4 | ~spl9_8),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f158])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    $false | (~spl9_3 | spl9_4 | ~spl9_8)),
% 0.21/0.47    inference(subsumption_resolution,[],[f157,f91])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    r2_hidden(sK3,k2_relat_1(sK2)) | ~spl9_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f89])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    spl9_8 <=> r2_hidden(sK3,k2_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    ~r2_hidden(sK3,k2_relat_1(sK2)) | (~spl9_3 | spl9_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f153,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl9_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl9_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    ~r2_hidden(sK3,k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl9_4),
% 0.21/0.47    inference(superposition,[],[f65,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) | spl9_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl9_4 <=> r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    ~spl9_7 | spl9_9),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f155])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    $false | (~spl9_7 | spl9_9)),
% 0.21/0.47    inference(subsumption_resolution,[],[f149,f99])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    ~sP6(sK3,sK2) | spl9_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f97])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    spl9_9 <=> sP6(sK3,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    sP6(sK3,sK2) | ~spl9_7),
% 0.21/0.47    inference(resolution,[],[f83,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | sP6(X2,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK4,sK3),sK2) | ~spl9_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl9_7 <=> r2_hidden(k4_tarski(sK4,sK3),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    spl9_8 | ~spl9_9),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f151])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    $false | (spl9_8 | ~spl9_9)),
% 0.21/0.47    inference(subsumption_resolution,[],[f150,f98])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    sP6(sK3,sK2) | ~spl9_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f97])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    ~sP6(sK3,sK2) | spl9_8),
% 0.21/0.47    inference(resolution,[],[f90,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X2,X0] : (r2_hidden(X2,k2_relat_1(X0)) | ~sP6(X2,X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~sP6(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ~r2_hidden(sK3,k2_relat_1(sK2)) | spl9_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f89])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    ~spl9_8 | ~spl9_11 | ~spl9_12 | ~spl9_15),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f147])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    $false | (~spl9_8 | ~spl9_11 | ~spl9_12 | ~spl9_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f146,f91])).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    ~r2_hidden(sK3,k2_relat_1(sK2)) | (~spl9_11 | ~spl9_12 | ~spl9_15)),
% 0.21/0.47    inference(forward_demodulation,[],[f143,f139])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) | ~spl9_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f137])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    spl9_15 <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | (~spl9_11 | ~spl9_12)),
% 0.21/0.47    inference(subsumption_resolution,[],[f142,f111])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    v1_relat_1(sK2) | ~spl9_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f110])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    spl9_11 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~spl9_12),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f141])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | ~spl9_12),
% 0.21/0.47    inference(resolution,[],[f128,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK8(sK3,X0,sK2),sK1) | ~r2_hidden(sK3,k9_relat_1(sK2,X0))) ) | ~spl9_12),
% 0.21/0.47    inference(resolution,[],[f115,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK8(sK3,X0,sK2),sK1) | ~r2_hidden(sK3,k9_relat_1(sK2,X0))) ) | ~spl9_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f114])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl9_12 <=> ! [X0] : (~m1_subset_1(sK8(sK3,X0,sK2),sK1) | ~r2_hidden(sK3,k9_relat_1(sK2,X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    spl9_15 | ~spl9_11 | ~spl9_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f135,f130,f110,f137])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    spl9_14 <=> sK2 = k7_relat_1(sK2,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) | (~spl9_11 | ~spl9_14)),
% 0.21/0.47    inference(subsumption_resolution,[],[f134,f111])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | ~spl9_14),
% 0.21/0.47    inference(superposition,[],[f29,f132])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    sK2 = k7_relat_1(sK2,sK1) | ~spl9_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f130])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    spl9_14 | ~spl9_6 | ~spl9_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f127,f110,f76,f130])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl9_6 <=> v4_relat_1(sK2,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    sK2 = k7_relat_1(sK2,sK1) | (~spl9_6 | ~spl9_11)),
% 0.21/0.47    inference(subsumption_resolution,[],[f85,f111])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | sK2 = k7_relat_1(sK2,sK1) | ~spl9_6),
% 0.21/0.47    inference(resolution,[],[f78,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    v4_relat_1(sK2,sK1) | ~spl9_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f76])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    ~spl9_3 | spl9_11),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    $false | (~spl9_3 | spl9_11)),
% 0.21/0.47    inference(subsumption_resolution,[],[f123,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | (~spl9_3 | spl9_11)),
% 0.21/0.47    inference(resolution,[],[f117,f60])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl9_11),
% 0.21/0.47    inference(resolution,[],[f112,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | spl9_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f110])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    ~spl9_11 | spl9_12 | ~spl9_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f95,f64,f114,f110])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK8(sK3,X0,sK2),sK1) | ~v1_relat_1(sK2) | ~r2_hidden(sK3,k9_relat_1(sK2,X0))) ) | ~spl9_4),
% 0.21/0.47    inference(resolution,[],[f93,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) ) | ~spl9_4),
% 0.21/0.47    inference(subsumption_resolution,[],[f21,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) | ~spl9_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f64])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X4] : (~m1_subset_1(X4,sK1) | ~r2_hidden(k4_tarski(X4,sK3),sK2) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f10])).
% 0.21/0.47  fof(f10,conjecture,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl9_8 | ~spl9_3 | ~spl9_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f87,f64,f58,f89])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    r2_hidden(sK3,k2_relat_1(sK2)) | (~spl9_3 | ~spl9_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f86,f60])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    r2_hidden(sK3,k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl9_4),
% 0.21/0.47    inference(superposition,[],[f66,f42])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    spl9_7 | spl9_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f74,f64,f81])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK4,sK3),sK2) | spl9_4),
% 0.21/0.47    inference(subsumption_resolution,[],[f23,f65])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK4,sK3),sK2) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl9_6 | ~spl9_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f62,f58,f76])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    v4_relat_1(sK2,sK1) | ~spl9_3),
% 0.21/0.47    inference(resolution,[],[f60,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl9_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f58])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (6790)------------------------------
% 0.21/0.47  % (6790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (6790)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (6790)Memory used [KB]: 10618
% 0.21/0.47  % (6790)Time elapsed: 0.053 s
% 0.21/0.47  % (6790)------------------------------
% 0.21/0.47  % (6790)------------------------------
% 0.21/0.47  % (6786)Success in time 0.114 s
%------------------------------------------------------------------------------

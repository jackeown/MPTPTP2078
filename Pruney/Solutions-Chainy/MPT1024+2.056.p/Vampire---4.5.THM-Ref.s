%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 226 expanded)
%              Number of leaves         :   32 (  96 expanded)
%              Depth                    :    9
%              Number of atoms          :  373 ( 676 expanded)
%              Number of equality atoms :   68 ( 110 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f287,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f72,f87,f91,f96,f116,f126,f130,f142,f155,f162,f174,f175,f179,f192,f207,f225,f260,f263,f286])).

% (29461)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f286,plain,
    ( spl8_23
    | ~ spl8_28 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | spl8_23
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f277,f54])).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f277,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5(k1_xboole_0,sK3))
    | spl8_23
    | ~ spl8_28 ),
    inference(superposition,[],[f191,f224])).

fof(f224,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl8_28
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f191,plain,
    ( ~ r1_tarski(sK0,sK5(sK0,sK3))
    | spl8_23 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl8_23
  <=> r1_tarski(sK0,sK5(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f263,plain,
    ( ~ spl8_27
    | spl8_30 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl8_27
    | spl8_30 ),
    inference(subsumption_resolution,[],[f261,f54])).

fof(f261,plain,
    ( ~ r1_tarski(k1_xboole_0,k4_tarski(sK7(sK4,sK2,k1_xboole_0),sK4))
    | ~ spl8_27
    | spl8_30 ),
    inference(forward_demodulation,[],[f259,f221])).

fof(f221,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl8_27
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f259,plain,
    ( ~ r1_tarski(sK3,k4_tarski(sK7(sK4,sK2,sK3),sK4))
    | spl8_30 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl8_30
  <=> r1_tarski(sK3,k4_tarski(sK7(sK4,sK2,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f260,plain,
    ( ~ spl8_30
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f146,f140,f258])).

fof(f140,plain,
    ( spl8_14
  <=> r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f146,plain,
    ( ~ r1_tarski(sK3,k4_tarski(sK7(sK4,sK2,sK3),sK4))
    | ~ spl8_14 ),
    inference(resolution,[],[f141,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f141,plain,
    ( r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f140])).

fof(f225,plain,
    ( spl8_27
    | spl8_28
    | ~ spl8_20
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f218,f205,f177,f223,f220])).

fof(f177,plain,
    ( spl8_20
  <=> v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f205,plain,
    ( spl8_26
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f218,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl8_20
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f208,f178])).

fof(f178,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f177])).

fof(f208,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl8_26 ),
    inference(resolution,[],[f206,f58])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f206,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f205])).

fof(f207,plain,
    ( spl8_26
    | ~ spl8_3
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f169,f160,f70,f205])).

fof(f70,plain,
    ( spl8_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f160,plain,
    ( spl8_17
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f169,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_3
    | ~ spl8_17 ),
    inference(superposition,[],[f71,f161])).

fof(f161,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f160])).

fof(f71,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f192,plain,
    ( ~ spl8_23
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f180,f172,f190])).

fof(f172,plain,
    ( spl8_19
  <=> r2_hidden(sK5(sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f180,plain,
    ( ~ r1_tarski(sK0,sK5(sK0,sK3))
    | ~ spl8_19 ),
    inference(resolution,[],[f173,f38])).

fof(f173,plain,
    ( r2_hidden(sK5(sK0,sK3),sK0)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f172])).

fof(f179,plain,
    ( spl8_20
    | ~ spl8_2
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f170,f160,f66,f177])).

fof(f66,plain,
    ( spl8_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f170,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl8_2
    | ~ spl8_17 ),
    inference(superposition,[],[f67,f161])).

fof(f67,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f175,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
    | r2_hidden(sK7(sK4,sK2,sK3),sK0)
    | ~ r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f174,plain,
    ( spl8_19
    | spl8_16
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f73,f70,f157,f172])).

fof(f157,plain,
    ( spl8_16
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f73,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | r2_hidden(sK5(sK0,sK3),sK0)
    | ~ spl8_3 ),
    inference(resolution,[],[f71,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK5(X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f162,plain,
    ( spl8_16
    | spl8_17
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f82,f70,f66,f160,f157])).

fof(f82,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f79,f67])).

fof(f79,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f71,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f155,plain,
    ( ~ spl8_15
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f151,f140,f114,f85,f62,f153])).

fof(f153,plain,
    ( spl8_15
  <=> r2_hidden(sK7(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f62,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f85,plain,
    ( spl8_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f114,plain,
    ( spl8_9
  <=> r2_hidden(sK7(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f151,plain,
    ( ~ r2_hidden(sK7(sK4,sK2,sK3),sK0)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f117,f150])).

fof(f150,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3))
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f149,f86])).

fof(f86,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f149,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f145,f63])).

fof(f63,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f145,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl8_14 ),
    inference(resolution,[],[f141,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f117,plain,
    ( ~ r2_hidden(sK7(sK4,sK2,sK3),sK0)
    | sK4 != k1_funct_1(sK3,sK7(sK4,sK2,sK3))
    | ~ spl8_9 ),
    inference(resolution,[],[f115,f26])).

fof(f26,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(f115,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f142,plain,
    ( spl8_14
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f102,f94,f85,f140])).

fof(f94,plain,
    ( spl8_6
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f102,plain,
    ( r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f98,f86])).

fof(f98,plain,
    ( r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_6 ),
    inference(resolution,[],[f95,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f95,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f130,plain,
    ( spl8_12
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f101,f94,f85,f128])).

fof(f128,plain,
    ( spl8_12
  <=> r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f101,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f97,f86])).

fof(f97,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl8_6 ),
    inference(resolution,[],[f95,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f126,plain,
    ( spl8_11
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f76,f70,f124])).

fof(f124,plain,
    ( spl8_11
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f76,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl8_3 ),
    inference(resolution,[],[f71,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f116,plain,
    ( spl8_9
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f103,f94,f85,f114])).

fof(f103,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f99,f86])).

fof(f99,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl8_6 ),
    inference(resolution,[],[f95,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f96,plain,
    ( spl8_6
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f92,f89,f70,f94])).

fof(f89,plain,
    ( spl8_5
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f92,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f90,f77])).

fof(f77,plain,
    ( ! [X2] : k7_relset_1(sK0,sK1,sK3,X2) = k9_relat_1(sK3,X2)
    | ~ spl8_3 ),
    inference(resolution,[],[f71,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f90,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f91,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f27,f89])).

fof(f27,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,
    ( spl8_4
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f83,f70,f85])).

fof(f83,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f81,f41])).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f81,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | ~ spl8_3 ),
    inference(resolution,[],[f71,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f72,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f68,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (29470)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (29472)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (29463)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (29466)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (29467)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (29459)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (29469)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (29458)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (29462)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (29460)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (29476)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (29471)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (29458)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f287,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f64,f68,f72,f87,f91,f96,f116,f126,f130,f142,f155,f162,f174,f175,f179,f192,f207,f225,f260,f263,f286])).
% 0.20/0.51  % (29461)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  fof(f286,plain,(
% 0.20/0.51    spl8_23 | ~spl8_28),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f285])).
% 0.20/0.51  fof(f285,plain,(
% 0.20/0.51    $false | (spl8_23 | ~spl8_28)),
% 0.20/0.51    inference(subsumption_resolution,[],[f277,f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.51  fof(f277,plain,(
% 0.20/0.51    ~r1_tarski(k1_xboole_0,sK5(k1_xboole_0,sK3)) | (spl8_23 | ~spl8_28)),
% 0.20/0.51    inference(superposition,[],[f191,f224])).
% 0.20/0.51  fof(f224,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | ~spl8_28),
% 0.20/0.51    inference(avatar_component_clause,[],[f223])).
% 0.20/0.51  fof(f223,plain,(
% 0.20/0.51    spl8_28 <=> k1_xboole_0 = sK0),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.20/0.51  fof(f191,plain,(
% 0.20/0.51    ~r1_tarski(sK0,sK5(sK0,sK3)) | spl8_23),
% 0.20/0.51    inference(avatar_component_clause,[],[f190])).
% 0.20/0.51  fof(f190,plain,(
% 0.20/0.51    spl8_23 <=> r1_tarski(sK0,sK5(sK0,sK3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.20/0.51  fof(f263,plain,(
% 0.20/0.51    ~spl8_27 | spl8_30),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f262])).
% 0.20/0.51  fof(f262,plain,(
% 0.20/0.51    $false | (~spl8_27 | spl8_30)),
% 0.20/0.51    inference(subsumption_resolution,[],[f261,f54])).
% 0.20/0.51  fof(f261,plain,(
% 0.20/0.51    ~r1_tarski(k1_xboole_0,k4_tarski(sK7(sK4,sK2,k1_xboole_0),sK4)) | (~spl8_27 | spl8_30)),
% 0.20/0.51    inference(forward_demodulation,[],[f259,f221])).
% 0.20/0.51  fof(f221,plain,(
% 0.20/0.51    k1_xboole_0 = sK3 | ~spl8_27),
% 0.20/0.51    inference(avatar_component_clause,[],[f220])).
% 0.20/0.51  fof(f220,plain,(
% 0.20/0.51    spl8_27 <=> k1_xboole_0 = sK3),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.20/0.51  fof(f259,plain,(
% 0.20/0.51    ~r1_tarski(sK3,k4_tarski(sK7(sK4,sK2,sK3),sK4)) | spl8_30),
% 0.20/0.51    inference(avatar_component_clause,[],[f258])).
% 0.20/0.51  fof(f258,plain,(
% 0.20/0.51    spl8_30 <=> r1_tarski(sK3,k4_tarski(sK7(sK4,sK2,sK3),sK4))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.20/0.51  fof(f260,plain,(
% 0.20/0.51    ~spl8_30 | ~spl8_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f146,f140,f258])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    spl8_14 <=> r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    ~r1_tarski(sK3,k4_tarski(sK7(sK4,sK2,sK3),sK4)) | ~spl8_14),
% 0.20/0.51    inference(resolution,[],[f141,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | ~spl8_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f140])).
% 0.20/0.51  fof(f225,plain,(
% 0.20/0.51    spl8_27 | spl8_28 | ~spl8_20 | ~spl8_26),
% 0.20/0.51    inference(avatar_split_clause,[],[f218,f205,f177,f223,f220])).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    spl8_20 <=> v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.20/0.51  fof(f205,plain,(
% 0.20/0.51    spl8_26 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.20/0.51  fof(f218,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | (~spl8_20 | ~spl8_26)),
% 0.20/0.51    inference(subsumption_resolution,[],[f208,f178])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl8_20),
% 0.20/0.51    inference(avatar_component_clause,[],[f177])).
% 0.20/0.51  fof(f208,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl8_26),
% 0.20/0.51    inference(resolution,[],[f206,f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(flattening,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.51  fof(f206,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl8_26),
% 0.20/0.51    inference(avatar_component_clause,[],[f205])).
% 0.20/0.51  fof(f207,plain,(
% 0.20/0.51    spl8_26 | ~spl8_3 | ~spl8_17),
% 0.20/0.51    inference(avatar_split_clause,[],[f169,f160,f70,f205])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    spl8_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.51  fof(f160,plain,(
% 0.20/0.51    spl8_17 <=> k1_xboole_0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.20/0.51  fof(f169,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl8_3 | ~spl8_17)),
% 0.20/0.51    inference(superposition,[],[f71,f161])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | ~spl8_17),
% 0.20/0.51    inference(avatar_component_clause,[],[f160])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f70])).
% 0.20/0.51  fof(f192,plain,(
% 0.20/0.51    ~spl8_23 | ~spl8_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f180,f172,f190])).
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    spl8_19 <=> r2_hidden(sK5(sK0,sK3),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.20/0.51  fof(f180,plain,(
% 0.20/0.51    ~r1_tarski(sK0,sK5(sK0,sK3)) | ~spl8_19),
% 0.20/0.51    inference(resolution,[],[f173,f38])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    r2_hidden(sK5(sK0,sK3),sK0) | ~spl8_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f172])).
% 0.20/0.51  fof(f179,plain,(
% 0.20/0.51    spl8_20 | ~spl8_2 | ~spl8_17),
% 0.20/0.51    inference(avatar_split_clause,[],[f170,f160,f66,f177])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    spl8_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl8_2 | ~spl8_17)),
% 0.20/0.51    inference(superposition,[],[f67,f161])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    v1_funct_2(sK3,sK0,sK1) | ~spl8_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f66])).
% 0.20/0.51  fof(f175,plain,(
% 0.20/0.51    sK0 != k1_relset_1(sK0,sK1,sK3) | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3) | r2_hidden(sK7(sK4,sK2,sK3),sK0) | ~r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    spl8_19 | spl8_16 | ~spl8_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f73,f70,f157,f172])).
% 0.20/0.51  fof(f157,plain,(
% 0.20/0.51    spl8_16 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    sK0 = k1_relset_1(sK0,sK1,sK3) | r2_hidden(sK5(sK0,sK3),sK0) | ~spl8_3),
% 0.20/0.51    inference(resolution,[],[f71,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK5(X1,X2),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    spl8_16 | spl8_17 | ~spl8_2 | ~spl8_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f82,f70,f66,f160,f157])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl8_2 | ~spl8_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f79,f67])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl8_3),
% 0.20/0.51    inference(resolution,[],[f71,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    ~spl8_15 | ~spl8_1 | ~spl8_4 | ~spl8_9 | ~spl8_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f151,f140,f114,f85,f62,f153])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    spl8_15 <=> r2_hidden(sK7(sK4,sK2,sK3),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    spl8_1 <=> v1_funct_1(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    spl8_4 <=> v1_relat_1(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    spl8_9 <=> r2_hidden(sK7(sK4,sK2,sK3),sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    ~r2_hidden(sK7(sK4,sK2,sK3),sK0) | (~spl8_1 | ~spl8_4 | ~spl8_9 | ~spl8_14)),
% 0.20/0.51    inference(subsumption_resolution,[],[f117,f150])).
% 0.20/0.51  fof(f150,plain,(
% 0.20/0.51    sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3)) | (~spl8_1 | ~spl8_4 | ~spl8_14)),
% 0.20/0.51    inference(subsumption_resolution,[],[f149,f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    v1_relat_1(sK3) | ~spl8_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f85])).
% 0.20/0.51  fof(f149,plain,(
% 0.20/0.51    sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3)) | ~v1_relat_1(sK3) | (~spl8_1 | ~spl8_14)),
% 0.20/0.51    inference(subsumption_resolution,[],[f145,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    v1_funct_1(sK3) | ~spl8_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f62])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3)) | ~v1_relat_1(sK3) | ~spl8_14),
% 0.20/0.51    inference(resolution,[],[f141,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    ~r2_hidden(sK7(sK4,sK2,sK3),sK0) | sK4 != k1_funct_1(sK3,sK7(sK4,sK2,sK3)) | ~spl8_9),
% 0.20/0.51    inference(resolution,[],[f115,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.20/0.51    inference(negated_conjecture,[],[f12])).
% 0.20/0.51  fof(f12,conjecture,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    r2_hidden(sK7(sK4,sK2,sK3),sK2) | ~spl8_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f114])).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    spl8_14 | ~spl8_4 | ~spl8_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f102,f94,f85,f140])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    spl8_6 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | (~spl8_4 | ~spl8_6)),
% 0.20/0.51    inference(subsumption_resolution,[],[f98,f86])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl8_6),
% 0.20/0.51    inference(resolution,[],[f95,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl8_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f94])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    spl8_12 | ~spl8_4 | ~spl8_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f101,f94,f85,f128])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    spl8_12 <=> r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) | (~spl8_4 | ~spl8_6)),
% 0.20/0.51    inference(subsumption_resolution,[],[f97,f86])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl8_6),
% 0.20/0.51    inference(resolution,[],[f95,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    spl8_11 | ~spl8_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f76,f70,f124])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    spl8_11 <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl8_3),
% 0.20/0.51    inference(resolution,[],[f71,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    spl8_9 | ~spl8_4 | ~spl8_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f103,f94,f85,f114])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    r2_hidden(sK7(sK4,sK2,sK3),sK2) | (~spl8_4 | ~spl8_6)),
% 0.20/0.51    inference(subsumption_resolution,[],[f99,f86])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    r2_hidden(sK7(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | ~spl8_6),
% 0.20/0.51    inference(resolution,[],[f95,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK7(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    spl8_6 | ~spl8_3 | ~spl8_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f92,f89,f70,f94])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl8_5 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl8_3 | ~spl8_5)),
% 0.20/0.51    inference(forward_demodulation,[],[f90,f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X2] : (k7_relset_1(sK0,sK1,sK3,X2) = k9_relat_1(sK3,X2)) ) | ~spl8_3),
% 0.20/0.51    inference(resolution,[],[f71,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl8_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f89])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    spl8_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f27,f89])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    spl8_4 | ~spl8_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f83,f70,f85])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    v1_relat_1(sK3) | ~spl8_3),
% 0.20/0.51    inference(subsumption_resolution,[],[f81,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) | ~spl8_3),
% 0.20/0.51    inference(resolution,[],[f71,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    spl8_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f30,f70])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    spl8_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f29,f66])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    spl8_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f28,f62])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    v1_funct_1(sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (29458)------------------------------
% 0.20/0.51  % (29458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (29458)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (29458)Memory used [KB]: 6268
% 0.20/0.51  % (29458)Time elapsed: 0.094 s
% 0.20/0.51  % (29458)------------------------------
% 0.20/0.51  % (29458)------------------------------
% 0.20/0.51  % (29468)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (29465)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.51  % (29464)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.52  % (29474)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.52  % (29459)Refutation not found, incomplete strategy% (29459)------------------------------
% 0.20/0.52  % (29459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29459)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (29459)Memory used [KB]: 10618
% 0.20/0.52  % (29459)Time elapsed: 0.100 s
% 0.20/0.52  % (29459)------------------------------
% 0.20/0.52  % (29459)------------------------------
% 0.20/0.52  % (29452)Success in time 0.162 s
%------------------------------------------------------------------------------

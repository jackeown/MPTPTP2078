%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 208 expanded)
%              Number of leaves         :   33 (  98 expanded)
%              Depth                    :    6
%              Number of atoms          :  376 ( 693 expanded)
%              Number of equality atoms :   41 ( 100 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f295,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f52,f56,f63,f67,f71,f103,f107,f111,f123,f127,f131,f138,f151,f155,f164,f169,f175,f198,f203,f209,f219,f226,f246,f278,f293])).

fof(f293,plain,
    ( ~ spl6_15
    | spl6_39
    | ~ spl6_46 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | ~ spl6_15
    | spl6_39
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f290,f245])).

fof(f245,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | spl6_39 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl6_39
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f290,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_15
    | ~ spl6_46 ),
    inference(superposition,[],[f102,f277])).

fof(f277,plain,
    ( k1_xboole_0 = sK5(k1_xboole_0)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl6_46
  <=> k1_xboole_0 = sK5(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f102,plain,
    ( ! [X0] : v1_partfun1(sK5(X0),X0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl6_15
  <=> ! [X0] : v1_partfun1(sK5(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f278,plain,
    ( spl6_46
    | ~ spl6_25
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f227,f224,f149,f276])).

fof(f149,plain,
    ( spl6_25
  <=> m1_subset_1(sK5(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f224,plain,
    ( spl6_37
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f227,plain,
    ( k1_xboole_0 = sK5(k1_xboole_0)
    | ~ spl6_25
    | ~ spl6_37 ),
    inference(resolution,[],[f225,f150])).

fof(f150,plain,
    ( m1_subset_1(sK5(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f149])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f224])).

fof(f246,plain,
    ( ~ spl6_39
    | spl6_32
    | ~ spl6_33
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f232,f224,f201,f196,f244])).

fof(f196,plain,
    ( spl6_32
  <=> v1_partfun1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f201,plain,
    ( spl6_33
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f232,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | spl6_32
    | ~ spl6_33
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f197,f228])).

fof(f228,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_33
    | ~ spl6_37 ),
    inference(resolution,[],[f225,f202])).

fof(f202,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f201])).

fof(f197,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | spl6_32 ),
    inference(avatar_component_clause,[],[f196])).

fof(f226,plain,
    ( spl6_37
    | ~ spl6_7
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f220,f217,f69,f224])).

fof(f69,plain,
    ( spl6_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f217,plain,
    ( spl6_36
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl6_7
    | ~ spl6_36 ),
    inference(resolution,[],[f218,f70])).

fof(f70,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f69])).

% (21613)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k1_xboole_0 = X0 )
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f217])).

fof(f219,plain,
    ( spl6_36
    | ~ spl6_22
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f140,f136,f129,f217])).

fof(f129,plain,
    ( spl6_22
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f136,plain,
    ( spl6_23
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl6_22
    | ~ spl6_23 ),
    inference(resolution,[],[f137,f130])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f129])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f136])).

fof(f209,plain,
    ( spl6_5
    | ~ spl6_23
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f181,f173,f136,f61])).

fof(f61,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f173,plain,
    ( spl6_30
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f181,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_23
    | ~ spl6_30 ),
    inference(resolution,[],[f174,f137])).

fof(f174,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f173])).

fof(f203,plain,
    ( spl6_33
    | ~ spl6_6
    | ~ spl6_17
    | ~ spl6_23
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f188,f173,f136,f109,f65,f201])).

fof(f65,plain,
    ( spl6_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f109,plain,
    ( spl6_17
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f188,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_6
    | ~ spl6_17
    | ~ spl6_23
    | ~ spl6_30 ),
    inference(forward_demodulation,[],[f186,f110])).

fof(f110,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f109])).

fof(f186,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_6
    | ~ spl6_23
    | ~ spl6_30 ),
    inference(backward_demodulation,[],[f66,f181])).

fof(f66,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f198,plain,
    ( ~ spl6_32
    | spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f191,f58,f50,f196])).

fof(f50,plain,
    ( spl6_2
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f58,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f191,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | spl6_2
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f51,f59])).

fof(f59,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f51,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f175,plain,
    ( spl6_30
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f171,f167,f65,f54,f173])).

fof(f54,plain,
    ( spl6_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f167,plain,
    ( spl6_29
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f171,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f170,f66])).

fof(f170,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3
    | ~ spl6_29 ),
    inference(resolution,[],[f168,f55])).

fof(f55,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f168,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,sK0,X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f167])).

fof(f169,plain,
    ( spl6_29
    | spl6_2
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f165,f162,f50,f167])).

fof(f162,plain,
    ( spl6_28
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f165,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) )
    | spl6_2
    | ~ spl6_28 ),
    inference(resolution,[],[f163,f51])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(sK2,X0)
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f162])).

fof(f164,plain,
    ( spl6_28
    | ~ spl6_1
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f156,f153,f46,f162])).

fof(f46,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f153,plain,
    ( spl6_26
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0) )
    | ~ spl6_1
    | ~ spl6_26 ),
    inference(resolution,[],[f154,f47])).

fof(f47,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f154,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f153])).

fof(f155,plain,(
    spl6_26 ),
    inference(avatar_split_clause,[],[f39,f153])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f151,plain,
    ( spl6_25
    | ~ spl6_17
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f133,f125,f109,f149])).

fof(f125,plain,
    ( spl6_21
  <=> ! [X0] : m1_subset_1(sK5(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f133,plain,
    ( m1_subset_1(sK5(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_17
    | ~ spl6_21 ),
    inference(superposition,[],[f126,f110])).

fof(f126,plain,
    ( ! [X0] : m1_subset_1(sK5(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f125])).

fof(f138,plain,
    ( spl6_23
    | ~ spl6_16
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f132,f121,f105,f136])).

fof(f105,plain,
    ( spl6_16
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f121,plain,
    ( spl6_20
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK4(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f132,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl6_16
    | ~ spl6_20 ),
    inference(resolution,[],[f122,f106])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f122,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f121])).

fof(f131,plain,(
    spl6_22 ),
    inference(avatar_split_clause,[],[f25,f129])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f127,plain,(
    spl6_21 ),
    inference(avatar_split_clause,[],[f30,f125])).

fof(f30,plain,(
    ! [X0] : m1_subset_1(sK5(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_partfun1(X1,X0)
      & v8_relat_2(X1)
      & v4_relat_2(X1)
      & v3_relat_2(X1)
      & v1_relat_2(X1)
      & v5_relat_1(X1,X0)
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_partfun1)).

fof(f123,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f29,f121])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f111,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f43,f109])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f107,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f27,f105])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f103,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f38,f101])).

fof(f38,plain,(
    ! [X0] : v1_partfun1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f71,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f24,f69])).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f67,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f22,f65])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

% (21613)Refutation not found, incomplete strategy% (21613)------------------------------
% (21613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

% (21613)Termination reason: Refutation not found, incomplete strategy

% (21613)Memory used [KB]: 10618
% (21613)Time elapsed: 0.090 s
% (21613)------------------------------
% (21613)------------------------------
fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) )
         => ( v1_partfun1(X2,X0)
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f63,plain,
    ( spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f17,f61,f58])).

fof(f17,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f56,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f21,f54])).

fof(f21,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    ~ v1_partfun1(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

% (21611)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f48,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:30:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (21598)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (21608)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (21606)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (21595)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (21606)Refutation not found, incomplete strategy% (21606)------------------------------
% 0.21/0.47  % (21606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (21606)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (21606)Memory used [KB]: 1663
% 0.21/0.47  % (21606)Time elapsed: 0.063 s
% 0.21/0.47  % (21606)------------------------------
% 0.21/0.47  % (21606)------------------------------
% 0.21/0.47  % (21608)Refutation not found, incomplete strategy% (21608)------------------------------
% 0.21/0.47  % (21608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (21608)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (21608)Memory used [KB]: 6140
% 0.21/0.47  % (21608)Time elapsed: 0.032 s
% 0.21/0.47  % (21608)------------------------------
% 0.21/0.47  % (21608)------------------------------
% 0.21/0.47  % (21595)Refutation not found, incomplete strategy% (21595)------------------------------
% 0.21/0.47  % (21595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (21595)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (21595)Memory used [KB]: 10618
% 0.21/0.47  % (21595)Time elapsed: 0.063 s
% 0.21/0.47  % (21595)------------------------------
% 0.21/0.47  % (21595)------------------------------
% 0.21/0.47  % (21596)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (21596)Refutation not found, incomplete strategy% (21596)------------------------------
% 0.21/0.48  % (21596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21596)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21596)Memory used [KB]: 10618
% 0.21/0.48  % (21596)Time elapsed: 0.062 s
% 0.21/0.48  % (21596)------------------------------
% 0.21/0.48  % (21596)------------------------------
% 0.21/0.48  % (21612)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (21603)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (21603)Refutation not found, incomplete strategy% (21603)------------------------------
% 0.21/0.48  % (21603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21603)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21603)Memory used [KB]: 6140
% 0.21/0.48  % (21603)Time elapsed: 0.075 s
% 0.21/0.48  % (21603)------------------------------
% 0.21/0.48  % (21603)------------------------------
% 0.21/0.48  % (21605)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (21605)Refutation not found, incomplete strategy% (21605)------------------------------
% 0.21/0.48  % (21605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21605)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21605)Memory used [KB]: 6012
% 0.21/0.48  % (21605)Time elapsed: 0.002 s
% 0.21/0.48  % (21605)------------------------------
% 0.21/0.48  % (21605)------------------------------
% 0.21/0.49  % (21604)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (21594)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (21604)Refutation not found, incomplete strategy% (21604)------------------------------
% 0.21/0.49  % (21604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (21604)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (21604)Memory used [KB]: 10618
% 0.21/0.49  % (21604)Time elapsed: 0.076 s
% 0.21/0.49  % (21604)------------------------------
% 0.21/0.49  % (21604)------------------------------
% 0.21/0.49  % (21594)Refutation not found, incomplete strategy% (21594)------------------------------
% 0.21/0.49  % (21594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (21594)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (21594)Memory used [KB]: 10618
% 0.21/0.49  % (21594)Time elapsed: 0.074 s
% 0.21/0.49  % (21594)------------------------------
% 0.21/0.49  % (21594)------------------------------
% 0.21/0.49  % (21597)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (21602)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (21609)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (21599)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (21602)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f48,f52,f56,f63,f67,f71,f103,f107,f111,f123,f127,f131,f138,f151,f155,f164,f169,f175,f198,f203,f209,f219,f226,f246,f278,f293])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    ~spl6_15 | spl6_39 | ~spl6_46),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f292])).
% 0.21/0.49  fof(f292,plain,(
% 0.21/0.49    $false | (~spl6_15 | spl6_39 | ~spl6_46)),
% 0.21/0.49    inference(subsumption_resolution,[],[f290,f245])).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | spl6_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f244])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    spl6_39 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    v1_partfun1(k1_xboole_0,k1_xboole_0) | (~spl6_15 | ~spl6_46)),
% 0.21/0.49    inference(superposition,[],[f102,f277])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    k1_xboole_0 = sK5(k1_xboole_0) | ~spl6_46),
% 0.21/0.49    inference(avatar_component_clause,[],[f276])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    spl6_46 <=> k1_xboole_0 = sK5(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ( ! [X0] : (v1_partfun1(sK5(X0),X0)) ) | ~spl6_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl6_15 <=> ! [X0] : v1_partfun1(sK5(X0),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    spl6_46 | ~spl6_25 | ~spl6_37),
% 0.21/0.49    inference(avatar_split_clause,[],[f227,f224,f149,f276])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    spl6_25 <=> m1_subset_1(sK5(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    spl6_37 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    k1_xboole_0 = sK5(k1_xboole_0) | (~spl6_25 | ~spl6_37)),
% 0.21/0.49    inference(resolution,[],[f225,f150])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    m1_subset_1(sK5(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl6_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f149])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl6_37),
% 0.21/0.49    inference(avatar_component_clause,[],[f224])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    ~spl6_39 | spl6_32 | ~spl6_33 | ~spl6_37),
% 0.21/0.49    inference(avatar_split_clause,[],[f232,f224,f201,f196,f244])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    spl6_32 <=> v1_partfun1(sK2,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    spl6_33 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | (spl6_32 | ~spl6_33 | ~spl6_37)),
% 0.21/0.49    inference(backward_demodulation,[],[f197,f228])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | (~spl6_33 | ~spl6_37)),
% 0.21/0.49    inference(resolution,[],[f225,f202])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl6_33),
% 0.21/0.49    inference(avatar_component_clause,[],[f201])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    ~v1_partfun1(sK2,k1_xboole_0) | spl6_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f196])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    spl6_37 | ~spl6_7 | ~spl6_36),
% 0.21/0.49    inference(avatar_split_clause,[],[f220,f217,f69,f224])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl6_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    spl6_36 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | (~spl6_7 | ~spl6_36)),
% 0.21/0.49    inference(resolution,[],[f218,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0) | ~spl6_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f69])).
% 0.21/0.49  % (21613)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_xboole_0 = X0) ) | ~spl6_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f217])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    spl6_36 | ~spl6_22 | ~spl6_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f140,f136,f129,f217])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    spl6_22 <=> ! [X1,X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    spl6_23 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1)) ) | (~spl6_22 | ~spl6_23)),
% 0.21/0.49    inference(resolution,[],[f137,f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) ) | ~spl6_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f129])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl6_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f136])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    spl6_5 | ~spl6_23 | ~spl6_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f181,f173,f136,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl6_5 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    spl6_30 <=> v1_xboole_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | (~spl6_23 | ~spl6_30)),
% 0.21/0.49    inference(resolution,[],[f174,f137])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    v1_xboole_0(sK1) | ~spl6_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f173])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    spl6_33 | ~spl6_6 | ~spl6_17 | ~spl6_23 | ~spl6_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f188,f173,f136,f109,f65,f201])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl6_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    spl6_17 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_6 | ~spl6_17 | ~spl6_23 | ~spl6_30)),
% 0.21/0.49    inference(forward_demodulation,[],[f186,f110])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl6_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f109])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl6_6 | ~spl6_23 | ~spl6_30)),
% 0.21/0.49    inference(backward_demodulation,[],[f66,f181])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f65])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    ~spl6_32 | spl6_2 | ~spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f191,f58,f50,f196])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl6_2 <=> v1_partfun1(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl6_4 <=> k1_xboole_0 = sK0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ~v1_partfun1(sK2,k1_xboole_0) | (spl6_2 | ~spl6_4)),
% 0.21/0.50    inference(backward_demodulation,[],[f51,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | ~spl6_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f58])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ~v1_partfun1(sK2,sK0) | spl6_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f50])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    spl6_30 | ~spl6_3 | ~spl6_6 | ~spl6_29),
% 0.21/0.50    inference(avatar_split_clause,[],[f171,f167,f65,f54,f173])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    spl6_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    spl6_29 <=> ! [X0] : (v1_xboole_0(X0) | ~v1_funct_2(sK2,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    v1_xboole_0(sK1) | (~spl6_3 | ~spl6_6 | ~spl6_29)),
% 0.21/0.50    inference(subsumption_resolution,[],[f170,f66])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    v1_xboole_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl6_3 | ~spl6_29)),
% 0.21/0.50    inference(resolution,[],[f168,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,sK1) | ~spl6_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f54])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_2(sK2,sK0,X0) | v1_xboole_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | ~spl6_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f167])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    spl6_29 | spl6_2 | ~spl6_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f165,f162,f50,f167])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl6_28 <=> ! [X1,X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(X0) | ~v1_funct_2(sK2,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | (spl6_2 | ~spl6_28)),
% 0.21/0.50    inference(resolution,[],[f163,f51])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_partfun1(sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f162])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    spl6_28 | ~spl6_1 | ~spl6_26),
% 0.21/0.50    inference(avatar_split_clause,[],[f156,f153,f46,f162])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    spl6_1 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    spl6_26 <=> ! [X1,X0,X2] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0)) ) | (~spl6_1 | ~spl6_26)),
% 0.21/0.50    inference(resolution,[],[f154,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    v1_funct_1(sK2) | ~spl6_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f46])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) ) | ~spl6_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f153])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    spl6_26),
% 0.21/0.50    inference(avatar_split_clause,[],[f39,f153])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    spl6_25 | ~spl6_17 | ~spl6_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f133,f125,f109,f149])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    spl6_21 <=> ! [X0] : m1_subset_1(sK5(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    m1_subset_1(sK5(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl6_17 | ~spl6_21)),
% 0.21/0.50    inference(superposition,[],[f126,f110])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(sK5(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl6_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f125])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl6_23 | ~spl6_16 | ~spl6_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f132,f121,f105,f136])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl6_16 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    spl6_20 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | (~spl6_16 | ~spl6_20)),
% 0.21/0.50    inference(resolution,[],[f122,f106])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) ) | ~spl6_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f105])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) ) | ~spl6_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f121])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl6_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f25,f129])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl6_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f125])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(sK5(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : ? [X1] : (v1_partfun1(X1,X0) & v8_relat_2(X1) & v4_relat_2(X1) & v3_relat_2(X1) & v1_relat_2(X1) & v5_relat_1(X1,X0) & v4_relat_1(X1,X0) & v1_relat_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_partfun1)).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    spl6_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f29,f121])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl6_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f109])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    spl6_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f105])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    spl6_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f38,f101])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0] : (v1_partfun1(sK5(X0),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    spl6_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f69])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    spl6_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f65])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f10])).
% 0.21/0.50  % (21613)Refutation not found, incomplete strategy% (21613)------------------------------
% 0.21/0.50  % (21613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (((~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  % (21613)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (21613)Memory used [KB]: 10618
% 0.21/0.50  % (21613)Time elapsed: 0.090 s
% 0.21/0.50  % (21613)------------------------------
% 0.21/0.50  % (21613)------------------------------
% 0.21/0.50  fof(f9,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.50    inference(negated_conjecture,[],[f8])).
% 0.21/0.50  fof(f8,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    spl6_4 | ~spl6_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f17,f61,f58])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    spl6_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f21,f54])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ~spl6_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f50])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ~v1_partfun1(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  % (21611)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f20,f46])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (21602)------------------------------
% 0.21/0.50  % (21602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21593)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (21602)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (21602)Memory used [KB]: 10746
% 0.21/0.50  % (21602)Time elapsed: 0.089 s
% 0.21/0.50  % (21602)------------------------------
% 0.21/0.50  % (21602)------------------------------
% 0.21/0.50  % (21592)Success in time 0.137 s
%------------------------------------------------------------------------------

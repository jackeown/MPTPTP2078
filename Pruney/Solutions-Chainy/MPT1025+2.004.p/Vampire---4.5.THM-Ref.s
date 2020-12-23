%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 218 expanded)
%              Number of leaves         :   31 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  364 ( 626 expanded)
%              Number of equality atoms :   63 (  88 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f288,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f82,f86,f98,f102,f107,f128,f139,f143,f166,f170,f193,f215,f221,f227,f237,f275,f279,f287])).

fof(f287,plain,
    ( ~ spl8_9
    | ~ spl8_31
    | ~ spl8_32 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_31
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f285,f274])).

fof(f274,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl8_31
  <=> sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f285,plain,
    ( sK4 != k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ spl8_9
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f284,f127])).

fof(f127,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl8_9
  <=> r2_hidden(sK6(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f284,plain,
    ( ~ r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | sK4 != k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ spl8_32 ),
    inference(resolution,[],[f278,f32])).

fof(f32,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ r2_hidden(X5,sK2)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(f278,plain,
    ( m1_subset_1(sK6(sK4,sK2,sK3),sK0)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl8_32
  <=> m1_subset_1(sK6(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f279,plain,
    ( spl8_32
    | ~ spl8_16
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f238,f223,f164,f277])).

fof(f164,plain,
    ( spl8_16
  <=> m1_subset_1(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f223,plain,
    ( spl8_26
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f238,plain,
    ( m1_subset_1(sK6(sK4,sK2,sK3),sK0)
    | ~ spl8_16
    | ~ spl8_26 ),
    inference(superposition,[],[f165,f224])).

fof(f224,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f223])).

fof(f165,plain,
    ( m1_subset_1(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f164])).

fof(f275,plain,
    ( spl8_31
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f181,f168,f96,f76,f273])).

fof(f76,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f96,plain,
    ( spl8_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f168,plain,
    ( spl8_17
  <=> r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f181,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f180,f97])).

fof(f97,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f180,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f173,f77])).

fof(f77,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f173,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl8_17 ),
    inference(resolution,[],[f169,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f169,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f168])).

fof(f237,plain,(
    ~ spl8_25 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f233,f58])).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f233,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_25 ),
    inference(resolution,[],[f220,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f220,plain,
    ( r2_hidden(sK7(sK3),k1_xboole_0)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl8_25
  <=> r2_hidden(sK7(sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f227,plain,
    ( spl8_26
    | ~ spl8_11
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f225,f188,f137,f223])).

fof(f137,plain,
    ( spl8_11
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f188,plain,
    ( spl8_19
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f225,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_11
    | ~ spl8_19 ),
    inference(superposition,[],[f189,f138])).

fof(f138,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f189,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f188])).

fof(f221,plain,
    ( spl8_25
    | ~ spl8_20
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f217,f213,f191,f219])).

fof(f191,plain,
    ( spl8_20
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f213,plain,
    ( spl8_24
  <=> r2_hidden(sK7(sK3),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f217,plain,
    ( r2_hidden(sK7(sK3),k1_xboole_0)
    | ~ spl8_20
    | ~ spl8_24 ),
    inference(forward_demodulation,[],[f216,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f216,plain,
    ( r2_hidden(sK7(sK3),k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl8_20
    | ~ spl8_24 ),
    inference(forward_demodulation,[],[f214,f192])).

fof(f192,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f191])).

fof(f214,plain,
    ( r2_hidden(sK7(sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f213])).

fof(f215,plain,
    ( spl8_24
    | ~ spl8_3
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f182,f168,f84,f213])).

fof(f84,plain,
    ( spl8_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f182,plain,
    ( r2_hidden(sK7(sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_3
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f158,f175])).

fof(f175,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl8_17 ),
    inference(resolution,[],[f169,f65])).

fof(f158,plain,
    ( r2_hidden(sK7(sK3),k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK3)
    | ~ spl8_3 ),
    inference(resolution,[],[f92,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f92,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK3)
        | r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f85,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f85,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f193,plain,
    ( spl8_19
    | spl8_20
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f93,f84,f80,f191,f188])).

fof(f80,plain,
    ( spl8_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f93,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f89,f81])).

fof(f81,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f89,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f85,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f170,plain,
    ( spl8_17
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f115,f105,f96,f168])).

fof(f105,plain,
    ( spl8_6
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f115,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f109,f97])).

fof(f109,plain,
    ( r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_6 ),
    inference(resolution,[],[f106,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f106,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f166,plain,
    ( spl8_16
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f150,f141,f164])).

fof(f141,plain,
    ( spl8_12
  <=> r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f150,plain,
    ( m1_subset_1(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl8_12 ),
    inference(resolution,[],[f142,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f142,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( spl8_12
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f114,f105,f96,f141])).

fof(f114,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f108,f97])).

fof(f108,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl8_6 ),
    inference(resolution,[],[f106,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f139,plain,
    ( spl8_11
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f87,f84,f137])).

fof(f87,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_3 ),
    inference(resolution,[],[f85,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f128,plain,
    ( spl8_9
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f116,f105,f96,f126])).

fof(f116,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f110,f97])).

fof(f110,plain,
    ( r2_hidden(sK6(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl8_6 ),
    inference(resolution,[],[f106,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f107,plain,
    ( spl8_6
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f103,f100,f84,f105])).

fof(f100,plain,
    ( spl8_5
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f103,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f101,f90])).

fof(f90,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl8_3 ),
    inference(resolution,[],[f85,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f101,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f33,f100])).

fof(f33,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f98,plain,
    ( spl8_4
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f94,f84,f96])).

fof(f94,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f91,f51])).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f91,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | ~ spl8_3 ),
    inference(resolution,[],[f85,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f86,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f36,f84])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f35,f80])).

fof(f35,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f78,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f34,f76])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:08:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (19947)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (19962)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (19947)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (19954)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (19960)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f288,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f78,f82,f86,f98,f102,f107,f128,f139,f143,f166,f170,f193,f215,f221,f227,f237,f275,f279,f287])).
% 0.22/0.49  fof(f287,plain,(
% 0.22/0.49    ~spl8_9 | ~spl8_31 | ~spl8_32),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f286])).
% 0.22/0.49  fof(f286,plain,(
% 0.22/0.49    $false | (~spl8_9 | ~spl8_31 | ~spl8_32)),
% 0.22/0.49    inference(subsumption_resolution,[],[f285,f274])).
% 0.22/0.49  fof(f274,plain,(
% 0.22/0.49    sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~spl8_31),
% 0.22/0.49    inference(avatar_component_clause,[],[f273])).
% 0.22/0.49  fof(f273,plain,(
% 0.22/0.49    spl8_31 <=> sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.22/0.49  fof(f285,plain,(
% 0.22/0.49    sK4 != k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | (~spl8_9 | ~spl8_32)),
% 0.22/0.49    inference(subsumption_resolution,[],[f284,f127])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~spl8_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f126])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    spl8_9 <=> r2_hidden(sK6(sK4,sK2,sK3),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.49  fof(f284,plain,(
% 0.22/0.49    ~r2_hidden(sK6(sK4,sK2,sK3),sK2) | sK4 != k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~spl8_32),
% 0.22/0.49    inference(resolution,[],[f278,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.49    inference(ennf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.49    inference(negated_conjecture,[],[f16])).
% 0.22/0.49  fof(f16,conjecture,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).
% 0.22/0.49  fof(f278,plain,(
% 0.22/0.49    m1_subset_1(sK6(sK4,sK2,sK3),sK0) | ~spl8_32),
% 0.22/0.49    inference(avatar_component_clause,[],[f277])).
% 0.22/0.49  fof(f277,plain,(
% 0.22/0.49    spl8_32 <=> m1_subset_1(sK6(sK4,sK2,sK3),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.22/0.49  fof(f279,plain,(
% 0.22/0.49    spl8_32 | ~spl8_16 | ~spl8_26),
% 0.22/0.49    inference(avatar_split_clause,[],[f238,f223,f164,f277])).
% 0.22/0.49  fof(f164,plain,(
% 0.22/0.49    spl8_16 <=> m1_subset_1(sK6(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.22/0.49  fof(f223,plain,(
% 0.22/0.49    spl8_26 <=> sK0 = k1_relat_1(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.22/0.49  fof(f238,plain,(
% 0.22/0.49    m1_subset_1(sK6(sK4,sK2,sK3),sK0) | (~spl8_16 | ~spl8_26)),
% 0.22/0.49    inference(superposition,[],[f165,f224])).
% 0.22/0.49  fof(f224,plain,(
% 0.22/0.49    sK0 = k1_relat_1(sK3) | ~spl8_26),
% 0.22/0.49    inference(avatar_component_clause,[],[f223])).
% 0.22/0.49  fof(f165,plain,(
% 0.22/0.49    m1_subset_1(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | ~spl8_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f164])).
% 0.22/0.49  fof(f275,plain,(
% 0.22/0.49    spl8_31 | ~spl8_1 | ~spl8_4 | ~spl8_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f181,f168,f96,f76,f273])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    spl8_1 <=> v1_funct_1(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    spl8_4 <=> v1_relat_1(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.49  fof(f168,plain,(
% 0.22/0.49    spl8_17 <=> r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | (~spl8_1 | ~spl8_4 | ~spl8_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f180,f97])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    v1_relat_1(sK3) | ~spl8_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f96])).
% 0.22/0.49  fof(f180,plain,(
% 0.22/0.49    sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~v1_relat_1(sK3) | (~spl8_1 | ~spl8_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f173,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    v1_funct_1(sK3) | ~spl8_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f76])).
% 0.22/0.49  fof(f173,plain,(
% 0.22/0.49    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK6(sK4,sK2,sK3)) | ~v1_relat_1(sK3) | ~spl8_17),
% 0.22/0.49    inference(resolution,[],[f169,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | ~spl8_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f168])).
% 0.22/0.49  fof(f237,plain,(
% 0.22/0.49    ~spl8_25),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f236])).
% 0.22/0.49  fof(f236,plain,(
% 0.22/0.49    $false | ~spl8_25),
% 0.22/0.49    inference(subsumption_resolution,[],[f233,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    ~v1_xboole_0(k1_xboole_0) | ~spl8_25),
% 0.22/0.49    inference(resolution,[],[f220,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    r2_hidden(sK7(sK3),k1_xboole_0) | ~spl8_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f219])).
% 0.22/0.49  fof(f219,plain,(
% 0.22/0.49    spl8_25 <=> r2_hidden(sK7(sK3),k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    spl8_26 | ~spl8_11 | ~spl8_19),
% 0.22/0.49    inference(avatar_split_clause,[],[f225,f188,f137,f223])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    spl8_11 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    spl8_19 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    sK0 = k1_relat_1(sK3) | (~spl8_11 | ~spl8_19)),
% 0.22/0.49    inference(superposition,[],[f189,f138])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl8_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f137])).
% 0.22/0.49  fof(f189,plain,(
% 0.22/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl8_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f188])).
% 0.22/0.49  fof(f221,plain,(
% 0.22/0.49    spl8_25 | ~spl8_20 | ~spl8_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f217,f213,f191,f219])).
% 0.22/0.49  fof(f191,plain,(
% 0.22/0.49    spl8_20 <=> k1_xboole_0 = sK1),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    spl8_24 <=> r2_hidden(sK7(sK3),k2_zfmisc_1(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.22/0.49  fof(f217,plain,(
% 0.22/0.49    r2_hidden(sK7(sK3),k1_xboole_0) | (~spl8_20 | ~spl8_24)),
% 0.22/0.49    inference(forward_demodulation,[],[f216,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.49  fof(f216,plain,(
% 0.22/0.49    r2_hidden(sK7(sK3),k2_zfmisc_1(sK0,k1_xboole_0)) | (~spl8_20 | ~spl8_24)),
% 0.22/0.49    inference(forward_demodulation,[],[f214,f192])).
% 0.22/0.49  fof(f192,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | ~spl8_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f191])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    r2_hidden(sK7(sK3),k2_zfmisc_1(sK0,sK1)) | ~spl8_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f213])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    spl8_24 | ~spl8_3 | ~spl8_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f182,f168,f84,f213])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    spl8_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    r2_hidden(sK7(sK3),k2_zfmisc_1(sK0,sK1)) | (~spl8_3 | ~spl8_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f158,f175])).
% 0.22/0.49  fof(f175,plain,(
% 0.22/0.49    ~v1_xboole_0(sK3) | ~spl8_17),
% 0.22/0.49    inference(resolution,[],[f169,f65])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    r2_hidden(sK7(sK3),k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(sK3) | ~spl8_3),
% 0.22/0.49    inference(resolution,[],[f92,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK7(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ( ! [X1] : (~r2_hidden(X1,sK3) | r2_hidden(X1,k2_zfmisc_1(sK0,sK1))) ) | ~spl8_3),
% 0.22/0.49    inference(resolution,[],[f85,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f84])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    spl8_19 | spl8_20 | ~spl8_2 | ~spl8_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f93,f84,f80,f191,f188])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    spl8_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl8_2 | ~spl8_3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f89,f81])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    v1_funct_2(sK3,sK0,sK1) | ~spl8_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f80])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl8_3),
% 0.22/0.49    inference(resolution,[],[f85,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(flattening,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    spl8_17 | ~spl8_4 | ~spl8_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f115,f105,f96,f168])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    spl8_6 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | (~spl8_4 | ~spl8_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f109,f97])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK6(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl8_6),
% 0.22/0.49    inference(resolution,[],[f106,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl8_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f105])).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    spl8_16 | ~spl8_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f150,f141,f164])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    spl8_12 <=> r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    m1_subset_1(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | ~spl8_12),
% 0.22/0.49    inference(resolution,[],[f142,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | ~spl8_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f141])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    spl8_12 | ~spl8_4 | ~spl8_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f114,f105,f96,f141])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | (~spl8_4 | ~spl8_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f108,f97])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    r2_hidden(sK6(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl8_6),
% 0.22/0.49    inference(resolution,[],[f106,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    spl8_11 | ~spl8_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f87,f84,f137])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl8_3),
% 0.22/0.49    inference(resolution,[],[f85,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    spl8_9 | ~spl8_4 | ~spl8_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f116,f105,f96,f126])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    r2_hidden(sK6(sK4,sK2,sK3),sK2) | (~spl8_4 | ~spl8_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f110,f97])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    r2_hidden(sK6(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3) | ~spl8_6),
% 0.22/0.49    inference(resolution,[],[f106,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    spl8_6 | ~spl8_3 | ~spl8_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f103,f100,f84,f105])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    spl8_5 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl8_3 | ~spl8_5)),
% 0.22/0.49    inference(forward_demodulation,[],[f101,f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl8_3),
% 0.22/0.49    inference(resolution,[],[f85,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl8_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f100])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl8_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f100])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    spl8_4 | ~spl8_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f94,f84,f96])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    v1_relat_1(sK3) | ~spl8_3),
% 0.22/0.49    inference(subsumption_resolution,[],[f91,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) | ~spl8_3),
% 0.22/0.49    inference(resolution,[],[f85,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    spl8_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f84])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    spl8_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f80])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    spl8_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f76])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    v1_funct_1(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (19947)------------------------------
% 0.22/0.49  % (19947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (19947)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (19947)Memory used [KB]: 6268
% 0.22/0.49  % (19947)Time elapsed: 0.060 s
% 0.22/0.49  % (19947)------------------------------
% 0.22/0.49  % (19947)------------------------------
% 0.22/0.49  % (19946)Success in time 0.132 s
%------------------------------------------------------------------------------

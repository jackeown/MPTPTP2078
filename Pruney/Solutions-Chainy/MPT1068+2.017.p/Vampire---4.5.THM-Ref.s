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
% DateTime   : Thu Dec  3 13:07:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 268 expanded)
%              Number of leaves         :   34 ( 106 expanded)
%              Depth                    :   12
%              Number of atoms          :  528 (1046 expanded)
%              Number of equality atoms :   97 ( 188 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f329,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f101,f107,f112,f126,f138,f173,f194,f200,f206,f209,f220,f243,f250,f285,f295,f309,f325,f328])).

fof(f328,plain,
    ( spl6_5
    | ~ spl6_36 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl6_5
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f326,f88])).

fof(f88,plain,
    ( k1_xboole_0 != sK1
    | spl6_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f326,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_36 ),
    inference(resolution,[],[f324,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f324,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl6_36
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f325,plain,
    ( spl6_36
    | ~ spl6_4
    | spl6_33 ),
    inference(avatar_split_clause,[],[f319,f306,f81,f322])).

fof(f81,plain,
    ( spl6_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f306,plain,
    ( spl6_33
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f319,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_4
    | spl6_33 ),
    inference(subsumption_resolution,[],[f318,f83])).

fof(f83,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f318,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5,sK1)
    | spl6_33 ),
    inference(resolution,[],[f308,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f308,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl6_33 ),
    inference(avatar_component_clause,[],[f306])).

fof(f309,plain,
    ( ~ spl6_33
    | ~ spl6_1
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_24
    | spl6_32 ),
    inference(avatar_split_clause,[],[f302,f292,f197,f188,f182,f66,f306])).

fof(f66,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f182,plain,
    ( spl6_21
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f188,plain,
    ( spl6_22
  <=> ! [X9,X10] :
        ( ~ v1_relat_1(X9)
        | k1_funct_1(k5_relat_1(sK3,X9),X10) = k1_funct_1(X9,k1_funct_1(sK3,X10))
        | ~ r2_hidden(X10,k1_relat_1(sK3))
        | ~ v1_funct_1(X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f197,plain,
    ( spl6_24
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f292,plain,
    ( spl6_32
  <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f302,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ spl6_1
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_24
    | spl6_32 ),
    inference(subsumption_resolution,[],[f301,f68])).

fof(f68,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f301,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ v1_funct_1(sK4)
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_24
    | spl6_32 ),
    inference(subsumption_resolution,[],[f300,f183])).

fof(f183,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f182])).

fof(f300,plain,
    ( ~ v1_relat_1(sK4)
    | ~ r2_hidden(sK5,sK1)
    | ~ v1_funct_1(sK4)
    | ~ spl6_22
    | ~ spl6_24
    | spl6_32 ),
    inference(trivial_inequality_removal,[],[f299])).

fof(f299,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v1_relat_1(sK4)
    | ~ r2_hidden(sK5,sK1)
    | ~ v1_funct_1(sK4)
    | ~ spl6_22
    | ~ spl6_24
    | spl6_32 ),
    inference(superposition,[],[f294,f210])).

fof(f210,plain,
    ( ! [X10,X9] :
        ( k1_funct_1(k5_relat_1(sK3,X9),X10) = k1_funct_1(X9,k1_funct_1(sK3,X10))
        | ~ v1_relat_1(X9)
        | ~ r2_hidden(X10,sK1)
        | ~ v1_funct_1(X9) )
    | ~ spl6_22
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f189,f199])).

fof(f199,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f197])).

fof(f189,plain,
    ( ! [X10,X9] :
        ( ~ v1_relat_1(X9)
        | k1_funct_1(k5_relat_1(sK3,X9),X10) = k1_funct_1(X9,k1_funct_1(sK3,X10))
        | ~ r2_hidden(X10,k1_relat_1(sK3))
        | ~ v1_funct_1(X9) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f188])).

fof(f294,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | spl6_32 ),
    inference(avatar_component_clause,[],[f292])).

fof(f295,plain,
    ( ~ spl6_32
    | spl6_12
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f290,f282,f135,f292])).

fof(f135,plain,
    ( spl6_12
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f282,plain,
    ( spl6_30
  <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f290,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | spl6_12
    | ~ spl6_30 ),
    inference(superposition,[],[f137,f284])).

fof(f284,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f282])).

fof(f137,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f135])).

fof(f285,plain,
    ( spl6_30
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f268,f217,f109,f104,f71,f66,f282])).

fof(f71,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f104,plain,
    ( spl6_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f109,plain,
    ( spl6_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f217,plain,
    ( spl6_25
  <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f268,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f267,f111])).

fof(f111,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f267,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f266,f106])).

fof(f106,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f266,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f264,f68])).

fof(f264,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_2
    | ~ spl6_25 ),
    inference(superposition,[],[f219,f93])).

fof(f93,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( k1_partfun1(X0,X1,X3,X4,sK3,X2) = k5_relat_1(sK3,X2)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_2 ),
    inference(resolution,[],[f73,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f73,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f219,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f217])).

fof(f250,plain,(
    spl6_27 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | spl6_27 ),
    inference(resolution,[],[f246,f42])).

fof(f42,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f246,plain,
    ( ! [X0] : ~ r1_xboole_0(k1_xboole_0,X0)
    | spl6_27 ),
    inference(subsumption_resolution,[],[f245,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f245,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ r1_xboole_0(k1_xboole_0,X0) )
    | spl6_27 ),
    inference(resolution,[],[f242,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f242,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_27 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl6_27
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

% (28241)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f243,plain,
    ( ~ spl6_27
    | spl6_3
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f225,f170,f76,f240])).

fof(f76,plain,
    ( spl6_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f170,plain,
    ( spl6_19
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f225,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_3
    | ~ spl6_19 ),
    inference(superposition,[],[f78,f172])).

fof(f172,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f170])).

fof(f78,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f220,plain,
    ( spl6_25
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | spl6_19 ),
    inference(avatar_split_clause,[],[f215,f170,f123,f109,f104,f98,f71,f66,f217])).

fof(f98,plain,
    ( spl6_6
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f123,plain,
    ( spl6_10
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f215,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | spl6_19 ),
    inference(subsumption_resolution,[],[f214,f68])).

fof(f214,plain,
    ( ~ v1_funct_1(sK4)
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | spl6_19 ),
    inference(subsumption_resolution,[],[f211,f106])).

fof(f211,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK4)
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | spl6_19 ),
    inference(resolution,[],[f203,f125])).

fof(f125,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ v1_funct_1(X0)
        | k8_funct_2(sK1,sK2,X1,sK3,X0) = k1_partfun1(sK1,sK2,sK2,X1,sK3,X0) )
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | spl6_19 ),
    inference(subsumption_resolution,[],[f202,f171])).

fof(f171,plain,
    ( k1_xboole_0 != sK2
    | spl6_19 ),
    inference(avatar_component_clause,[],[f170])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,X0))
        | k1_xboole_0 = sK2
        | k8_funct_2(sK1,sK2,X1,sK3,X0) = k1_partfun1(sK1,sK2,sK2,X1,sK3,X0) )
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f201,f111])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,X0))
        | k1_xboole_0 = sK2
        | k8_funct_2(sK1,sK2,X1,sK3,X0) = k1_partfun1(sK1,sK2,sK2,X1,sK3,X0) )
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(resolution,[],[f94,f100])).

fof(f100,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f94,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ v1_funct_2(sK3,X5,X6)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_1(X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X8)))
        | ~ r1_tarski(k2_relset_1(X5,X6,sK3),k1_relset_1(X6,X8,X7))
        | k1_xboole_0 = X6
        | k8_funct_2(X5,X6,X8,sK3,X7) = k1_partfun1(X5,X6,X6,X8,sK3,X7) )
    | ~ spl6_2 ),
    inference(resolution,[],[f73,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | k1_xboole_0 = X1
      | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

fof(f209,plain,
    ( ~ spl6_8
    | spl6_23 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl6_8
    | spl6_23 ),
    inference(resolution,[],[f195,f111])).

fof(f195,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_23 ),
    inference(resolution,[],[f193,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f193,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_23 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl6_23
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f206,plain,
    ( ~ spl6_7
    | spl6_21 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl6_7
    | spl6_21 ),
    inference(resolution,[],[f186,f106])).

fof(f186,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_21 ),
    inference(resolution,[],[f184,f50])).

fof(f184,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f182])).

fof(f200,plain,
    ( spl6_24
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f176,f166,f109,f197])).

fof(f166,plain,
    ( spl6_18
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f176,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f174,f111])).

fof(f174,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_18 ),
    inference(superposition,[],[f168,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f168,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f194,plain,
    ( spl6_22
    | ~ spl6_23
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f95,f71,f191,f188])).

fof(f95,plain,
    ( ! [X10,X9] :
        ( ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ r2_hidden(X10,k1_relat_1(sK3))
        | k1_funct_1(k5_relat_1(sK3,X9),X10) = k1_funct_1(X9,k1_funct_1(sK3,X10)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f73,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f173,plain,
    ( spl6_18
    | spl6_19
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f159,f109,f98,f170,f166])).

fof(f159,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f102,f111])).

fof(f102,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_6 ),
    inference(resolution,[],[f100,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f138,plain,(
    ~ spl6_12 ),
    inference(avatar_split_clause,[],[f35,f135])).

fof(f35,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f126,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f33,f123])).

fof(f33,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f16])).

fof(f112,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f40,f109])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f107,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f37,f104])).

fof(f37,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f101,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f39,f98])).

fof(f39,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f89,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f34,f86])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f84,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f32,f81])).

fof(f32,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f79,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f41,f76])).

fof(f41,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f74,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f38,f71])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:26:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (28242)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (28243)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (28248)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (28249)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (28243)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (28245)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (28252)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (28240)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (28252)Refutation not found, incomplete strategy% (28252)------------------------------
% 0.22/0.49  % (28252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f329,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f101,f107,f112,f126,f138,f173,f194,f200,f206,f209,f220,f243,f250,f285,f295,f309,f325,f328])).
% 0.22/0.49  fof(f328,plain,(
% 0.22/0.49    spl6_5 | ~spl6_36),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f327])).
% 0.22/0.49  fof(f327,plain,(
% 0.22/0.49    $false | (spl6_5 | ~spl6_36)),
% 0.22/0.49    inference(subsumption_resolution,[],[f326,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    k1_xboole_0 != sK1 | spl6_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f86])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    spl6_5 <=> k1_xboole_0 = sK1),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.49  fof(f326,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | ~spl6_36),
% 0.22/0.49    inference(resolution,[],[f324,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.49  fof(f324,plain,(
% 0.22/0.49    v1_xboole_0(sK1) | ~spl6_36),
% 0.22/0.49    inference(avatar_component_clause,[],[f322])).
% 0.22/0.49  fof(f322,plain,(
% 0.22/0.49    spl6_36 <=> v1_xboole_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.22/0.49  fof(f325,plain,(
% 0.22/0.49    spl6_36 | ~spl6_4 | spl6_33),
% 0.22/0.49    inference(avatar_split_clause,[],[f319,f306,f81,f322])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    spl6_4 <=> m1_subset_1(sK5,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.49  fof(f306,plain,(
% 0.22/0.49    spl6_33 <=> r2_hidden(sK5,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.22/0.49  fof(f319,plain,(
% 0.22/0.49    v1_xboole_0(sK1) | (~spl6_4 | spl6_33)),
% 0.22/0.49    inference(subsumption_resolution,[],[f318,f83])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    m1_subset_1(sK5,sK1) | ~spl6_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f81])).
% 0.22/0.49  fof(f318,plain,(
% 0.22/0.49    v1_xboole_0(sK1) | ~m1_subset_1(sK5,sK1) | spl6_33),
% 0.22/0.49    inference(resolution,[],[f308,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.49  fof(f308,plain,(
% 0.22/0.49    ~r2_hidden(sK5,sK1) | spl6_33),
% 0.22/0.49    inference(avatar_component_clause,[],[f306])).
% 0.22/0.49  fof(f309,plain,(
% 0.22/0.49    ~spl6_33 | ~spl6_1 | ~spl6_21 | ~spl6_22 | ~spl6_24 | spl6_32),
% 0.22/0.49    inference(avatar_split_clause,[],[f302,f292,f197,f188,f182,f66,f306])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl6_1 <=> v1_funct_1(sK4)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    spl6_21 <=> v1_relat_1(sK4)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    spl6_22 <=> ! [X9,X10] : (~v1_relat_1(X9) | k1_funct_1(k5_relat_1(sK3,X9),X10) = k1_funct_1(X9,k1_funct_1(sK3,X10)) | ~r2_hidden(X10,k1_relat_1(sK3)) | ~v1_funct_1(X9))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    spl6_24 <=> sK1 = k1_relat_1(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.49  fof(f292,plain,(
% 0.22/0.49    spl6_32 <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.22/0.49  fof(f302,plain,(
% 0.22/0.49    ~r2_hidden(sK5,sK1) | (~spl6_1 | ~spl6_21 | ~spl6_22 | ~spl6_24 | spl6_32)),
% 0.22/0.49    inference(subsumption_resolution,[],[f301,f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    v1_funct_1(sK4) | ~spl6_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f66])).
% 0.22/0.49  fof(f301,plain,(
% 0.22/0.49    ~r2_hidden(sK5,sK1) | ~v1_funct_1(sK4) | (~spl6_21 | ~spl6_22 | ~spl6_24 | spl6_32)),
% 0.22/0.49    inference(subsumption_resolution,[],[f300,f183])).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    v1_relat_1(sK4) | ~spl6_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f182])).
% 0.22/0.50  fof(f300,plain,(
% 0.22/0.50    ~v1_relat_1(sK4) | ~r2_hidden(sK5,sK1) | ~v1_funct_1(sK4) | (~spl6_22 | ~spl6_24 | spl6_32)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f299])).
% 0.22/0.50  fof(f299,plain,(
% 0.22/0.50    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v1_relat_1(sK4) | ~r2_hidden(sK5,sK1) | ~v1_funct_1(sK4) | (~spl6_22 | ~spl6_24 | spl6_32)),
% 0.22/0.50    inference(superposition,[],[f294,f210])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    ( ! [X10,X9] : (k1_funct_1(k5_relat_1(sK3,X9),X10) = k1_funct_1(X9,k1_funct_1(sK3,X10)) | ~v1_relat_1(X9) | ~r2_hidden(X10,sK1) | ~v1_funct_1(X9)) ) | (~spl6_22 | ~spl6_24)),
% 0.22/0.50    inference(forward_demodulation,[],[f189,f199])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    sK1 = k1_relat_1(sK3) | ~spl6_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f197])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    ( ! [X10,X9] : (~v1_relat_1(X9) | k1_funct_1(k5_relat_1(sK3,X9),X10) = k1_funct_1(X9,k1_funct_1(sK3,X10)) | ~r2_hidden(X10,k1_relat_1(sK3)) | ~v1_funct_1(X9)) ) | ~spl6_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f188])).
% 0.22/0.50  fof(f294,plain,(
% 0.22/0.50    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | spl6_32),
% 0.22/0.50    inference(avatar_component_clause,[],[f292])).
% 0.22/0.50  fof(f295,plain,(
% 0.22/0.50    ~spl6_32 | spl6_12 | ~spl6_30),
% 0.22/0.50    inference(avatar_split_clause,[],[f290,f282,f135,f292])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    spl6_12 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.50  fof(f282,plain,(
% 0.22/0.50    spl6_30 <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.22/0.50  fof(f290,plain,(
% 0.22/0.50    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | (spl6_12 | ~spl6_30)),
% 0.22/0.50    inference(superposition,[],[f137,f284])).
% 0.22/0.50  fof(f284,plain,(
% 0.22/0.50    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | ~spl6_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f282])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl6_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f135])).
% 0.22/0.50  fof(f285,plain,(
% 0.22/0.50    spl6_30 | ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_25),
% 0.22/0.50    inference(avatar_split_clause,[],[f268,f217,f109,f104,f71,f66,f282])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    spl6_2 <=> v1_funct_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    spl6_7 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    spl6_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    spl6_25 <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.22/0.50  fof(f268,plain,(
% 0.22/0.50    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_25)),
% 0.22/0.50    inference(subsumption_resolution,[],[f267,f111])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f109])).
% 0.22/0.50  fof(f267,plain,(
% 0.22/0.50    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_25)),
% 0.22/0.50    inference(subsumption_resolution,[],[f266,f106])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl6_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f104])).
% 0.22/0.50  fof(f266,plain,(
% 0.22/0.50    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_1 | ~spl6_2 | ~spl6_25)),
% 0.22/0.50    inference(subsumption_resolution,[],[f264,f68])).
% 0.22/0.50  fof(f264,plain,(
% 0.22/0.50    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_2 | ~spl6_25)),
% 0.22/0.50    inference(superposition,[],[f219,f93])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (k1_partfun1(X0,X1,X3,X4,sK3,X2) = k5_relat_1(sK3,X2) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_2),
% 0.22/0.50    inference(resolution,[],[f73,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.50    inference(flattening,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    v1_funct_1(sK3) | ~spl6_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f71])).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~spl6_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f217])).
% 0.22/0.50  fof(f250,plain,(
% 0.22/0.50    spl6_27),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f249])).
% 0.22/0.50  fof(f249,plain,(
% 0.22/0.50    $false | spl6_27),
% 0.22/0.50    inference(resolution,[],[f246,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.50  fof(f246,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0)) ) | spl6_27),
% 0.22/0.50    inference(subsumption_resolution,[],[f245,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.50  fof(f245,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~r1_xboole_0(k1_xboole_0,X0)) ) | spl6_27),
% 0.22/0.50    inference(resolution,[],[f242,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.22/0.50  fof(f242,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0) | spl6_27),
% 0.22/0.50    inference(avatar_component_clause,[],[f240])).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    spl6_27 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.22/0.50  % (28241)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  fof(f243,plain,(
% 0.22/0.50    ~spl6_27 | spl6_3 | ~spl6_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f225,f170,f76,f240])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    spl6_3 <=> v1_xboole_0(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    spl6_19 <=> k1_xboole_0 = sK2),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0) | (spl6_3 | ~spl6_19)),
% 0.22/0.50    inference(superposition,[],[f78,f172])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | ~spl6_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f170])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ~v1_xboole_0(sK2) | spl6_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f76])).
% 0.22/0.50  fof(f220,plain,(
% 0.22/0.50    spl6_25 | ~spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10 | spl6_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f215,f170,f123,f109,f104,f98,f71,f66,f217])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    spl6_6 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    spl6_10 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | (~spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10 | spl6_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f214,f68])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    ~v1_funct_1(sK4) | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | (~spl6_2 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10 | spl6_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f211,f106])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_10 | spl6_19)),
% 0.22/0.50    inference(resolution,[],[f203,f125])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl6_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f123])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~v1_funct_1(X0) | k8_funct_2(sK1,sK2,X1,sK3,X0) = k1_partfun1(sK1,sK2,sK2,X1,sK3,X0)) ) | (~spl6_2 | ~spl6_6 | ~spl6_8 | spl6_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f202,f171])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    k1_xboole_0 != sK2 | spl6_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f170])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,X0)) | k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,X1,sK3,X0) = k1_partfun1(sK1,sK2,sK2,X1,sK3,X0)) ) | (~spl6_2 | ~spl6_6 | ~spl6_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f201,f111])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,X0)) | k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,X1,sK3,X0) = k1_partfun1(sK1,sK2,sK2,X1,sK3,X0)) ) | (~spl6_2 | ~spl6_6)),
% 0.22/0.50    inference(resolution,[],[f94,f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK1,sK2) | ~spl6_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f98])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ( ! [X6,X8,X7,X5] : (~v1_funct_2(sK3,X5,X6) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_1(X7) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X8))) | ~r1_tarski(k2_relset_1(X5,X6,sK3),k1_relset_1(X6,X8,X7)) | k1_xboole_0 = X6 | k8_funct_2(X5,X6,X8,sK3,X7) = k1_partfun1(X5,X6,X6,X8,sK3,X7)) ) | ~spl6_2),
% 0.22/0.50    inference(resolution,[],[f73,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | k1_xboole_0 = X1 | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    ~spl6_8 | spl6_23),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f207])).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    $false | (~spl6_8 | spl6_23)),
% 0.22/0.50    inference(resolution,[],[f195,f111])).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_23),
% 0.22/0.50    inference(resolution,[],[f193,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    ~v1_relat_1(sK3) | spl6_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f191])).
% 0.22/0.50  fof(f191,plain,(
% 0.22/0.50    spl6_23 <=> v1_relat_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    ~spl6_7 | spl6_21),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f204])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    $false | (~spl6_7 | spl6_21)),
% 0.22/0.50    inference(resolution,[],[f186,f106])).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_21),
% 0.22/0.50    inference(resolution,[],[f184,f50])).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    ~v1_relat_1(sK4) | spl6_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f182])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    spl6_24 | ~spl6_8 | ~spl6_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f176,f166,f109,f197])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    spl6_18 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    sK1 = k1_relat_1(sK3) | (~spl6_8 | ~spl6_18)),
% 0.22/0.50    inference(subsumption_resolution,[],[f174,f111])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_18),
% 0.22/0.50    inference(superposition,[],[f168,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl6_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f166])).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    spl6_22 | ~spl6_23 | ~spl6_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f95,f71,f191,f188])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ( ! [X10,X9] : (~v1_relat_1(sK3) | ~v1_relat_1(X9) | ~v1_funct_1(X9) | ~r2_hidden(X10,k1_relat_1(sK3)) | k1_funct_1(k5_relat_1(sK3,X9),X10) = k1_funct_1(X9,k1_funct_1(sK3,X10))) ) | ~spl6_2),
% 0.22/0.50    inference(resolution,[],[f73,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    spl6_18 | spl6_19 | ~spl6_6 | ~spl6_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f159,f109,f98,f170,f166])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | (~spl6_6 | ~spl6_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f102,f111])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_6),
% 0.22/0.50    inference(resolution,[],[f100,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    ~spl6_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f35,f135])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f13])).
% 0.22/0.50  fof(f13,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    spl6_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f33,f123])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    spl6_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f40,f109])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    spl6_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f104])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl6_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f39,f98])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ~spl6_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f34,f86])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    k1_xboole_0 != sK1),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl6_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f32,f81])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    m1_subset_1(sK5,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ~spl6_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f41,f76])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ~v1_xboole_0(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    spl6_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f38,f71])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    v1_funct_1(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl6_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f36,f66])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    v1_funct_1(sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (28243)------------------------------
% 0.22/0.50  % (28243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28243)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (28243)Memory used [KB]: 10874
% 0.22/0.50  % (28243)Time elapsed: 0.072 s
% 0.22/0.50  % (28243)------------------------------
% 0.22/0.50  % (28243)------------------------------
% 0.22/0.50  % (28241)Refutation not found, incomplete strategy% (28241)------------------------------
% 0.22/0.50  % (28241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28241)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (28241)Memory used [KB]: 10618
% 0.22/0.50  % (28241)Time elapsed: 0.079 s
% 0.22/0.50  % (28241)------------------------------
% 0.22/0.50  % (28241)------------------------------
% 0.22/0.50  % (28239)Success in time 0.137 s
%------------------------------------------------------------------------------

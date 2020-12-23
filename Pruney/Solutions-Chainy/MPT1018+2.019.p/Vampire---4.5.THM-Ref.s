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
% DateTime   : Thu Dec  3 13:05:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 226 expanded)
%              Number of leaves         :   30 (  99 expanded)
%              Depth                    :   10
%              Number of atoms          :  330 ( 953 expanded)
%              Number of equality atoms :   76 ( 243 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f249,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f80,f84,f88,f92,f96,f169,f178,f184,f190,f207,f211,f219,f226,f240,f247,f248])).

fof(f248,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK3
    | sK2 = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f247,plain,
    ( spl4_29
    | ~ spl4_9
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f242,f238,f94,f245])).

fof(f245,plain,
    ( spl4_29
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f94,plain,
    ( spl4_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f238,plain,
    ( spl4_28
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f242,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_9
    | ~ spl4_28 ),
    inference(resolution,[],[f239,f103])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_9 ),
    inference(resolution,[],[f55,f95])).

fof(f95,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f239,plain,
    ( v1_xboole_0(sK3)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f238])).

fof(f240,plain,
    ( spl4_28
    | ~ spl4_9
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f236,f209,f94,f238])).

fof(f209,plain,
    ( spl4_23
  <=> r2_hidden(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f236,plain,
    ( v1_xboole_0(sK3)
    | ~ spl4_9
    | ~ spl4_23 ),
    inference(resolution,[],[f210,f112])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | v1_xboole_0(X0) )
    | ~ spl4_9 ),
    inference(resolution,[],[f109,f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f109,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
        | ~ r2_hidden(X1,X0)
        | v1_xboole_0(X1) )
    | ~ spl4_9 ),
    inference(resolution,[],[f57,f107])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f106,f60])).

fof(f60,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f53])).

% (9249)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_xboole_0(X0) )
    | ~ spl4_9 ),
    inference(resolution,[],[f49,f95])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f210,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f209])).

fof(f226,plain,
    ( spl4_25
    | ~ spl4_9
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f221,f217,f94,f224])).

fof(f224,plain,
    ( spl4_25
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f217,plain,
    ( spl4_24
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f221,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_9
    | ~ spl4_24 ),
    inference(resolution,[],[f218,f103])).

fof(f218,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f217])).

fof(f219,plain,
    ( spl4_24
    | ~ spl4_9
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f215,f205,f94,f217])).

fof(f205,plain,
    ( spl4_22
  <=> r2_hidden(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f215,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_9
    | ~ spl4_22 ),
    inference(resolution,[],[f206,f112])).

fof(f206,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f205])).

fof(f211,plain,
    ( spl4_23
    | ~ spl4_3
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f194,f176,f70,f209])).

fof(f70,plain,
    ( spl4_3
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f176,plain,
    ( spl4_18
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f194,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_18 ),
    inference(superposition,[],[f71,f177])).

fof(f177,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f176])).

fof(f71,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f207,plain,
    ( spl4_22
    | ~ spl4_4
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f193,f176,f74,f205])).

fof(f74,plain,
    ( spl4_4
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f193,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_18 ),
    inference(superposition,[],[f75,f177])).

fof(f75,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f190,plain,
    ( ~ spl4_4
    | spl4_1
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f186,f182,f173,f62,f74])).

fof(f62,plain,
    ( spl4_1
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f173,plain,
    ( spl4_17
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f182,plain,
    ( spl4_19
  <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f186,plain,
    ( sK2 = sK3
    | ~ r2_hidden(sK2,sK0)
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(superposition,[],[f174,f183])).

fof(f183,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f182])).

fof(f174,plain,
    ( ! [X0] :
        ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f173])).

fof(f184,plain,
    ( ~ spl4_3
    | spl4_19
    | ~ spl4_2
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f179,f173,f66,f182,f70])).

fof(f66,plain,
    ( spl4_2
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f179,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ r2_hidden(sK3,sK0)
    | ~ spl4_2
    | ~ spl4_17 ),
    inference(superposition,[],[f174,f67])).

fof(f67,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f178,plain,
    ( ~ spl4_6
    | spl4_17
    | spl4_18
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f170,f167,f86,f176,f173,f82])).

fof(f82,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f86,plain,
    ( spl4_7
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f167,plain,
    ( spl4_16
  <=> ! [X1,X0,X2] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_2(sK1,X2,X0)
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f170,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | ~ r2_hidden(X0,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(resolution,[],[f168,f87])).

fof(f87,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f168,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK1,X2,X0)
        | k1_xboole_0 = X0
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1 )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f167])).

fof(f169,plain,
    ( ~ spl4_8
    | spl4_16
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f165,f78,f167,f90])).

fof(f90,plain,
    ( spl4_8
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f78,plain,
    ( spl4_5
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f165,plain,
    ( ! [X2,X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(X1,X2)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_2(sK1,X2,X0)
        | ~ v1_funct_1(sK1) )
    | ~ spl4_5 ),
    inference(resolution,[],[f58,f79])).

fof(f79,plain,
    ( v2_funct_1(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(f96,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f43,f94])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f92,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f35,f90])).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK2 != sK3
    & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    & r2_hidden(sK3,sK0)
    & r2_hidden(sK2,sK0)
    & v2_funct_1(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X3,X2] :
          ( X2 != X3
          & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
          & r2_hidden(X3,sK0)
          & r2_hidden(X2,sK0) )
      & v2_funct_1(sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK0)
        & r2_hidden(X2,sK0) )
   => ( sK2 != sK3
      & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK0)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

fof(f88,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f36,f86])).

fof(f36,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f37,f82])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f38,f78])).

fof(f38,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f40,f70])).

fof(f40,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f41,f66])).

fof(f41,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f42,f62])).

fof(f42,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:11:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (9254)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (9253)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (9254)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (9262)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f249,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f80,f84,f88,f92,f96,f169,f178,f184,f190,f207,f211,f219,f226,f240,f247,f248])).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    k1_xboole_0 != sK2 | k1_xboole_0 != sK3 | sK2 = sK3),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    spl4_29 | ~spl4_9 | ~spl4_28),
% 0.21/0.48    inference(avatar_split_clause,[],[f242,f238,f94,f245])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    spl4_29 <=> k1_xboole_0 = sK3),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl4_9 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f238,plain,(
% 0.21/0.48    spl4_28 <=> v1_xboole_0(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    k1_xboole_0 = sK3 | (~spl4_9 | ~spl4_28)),
% 0.21/0.48    inference(resolution,[],[f239,f103])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl4_9),
% 0.21/0.48    inference(resolution,[],[f55,f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0) | ~spl4_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f94])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    v1_xboole_0(sK3) | ~spl4_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f238])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    spl4_28 | ~spl4_9 | ~spl4_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f236,f209,f94,f238])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    spl4_23 <=> r2_hidden(sK3,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    v1_xboole_0(sK3) | (~spl4_9 | ~spl4_23)),
% 0.21/0.48    inference(resolution,[],[f210,f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | v1_xboole_0(X0)) ) | ~spl4_9),
% 0.21/0.48    inference(resolution,[],[f109,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~r2_hidden(X1,X0) | v1_xboole_0(X1)) ) | ~spl4_9),
% 0.21/0.48    inference(resolution,[],[f57,f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl4_9),
% 0.21/0.48    inference(forward_demodulation,[],[f106,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f53])).
% 0.21/0.48  % (9249)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    inference(flattening,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(X0)) ) | ~spl4_9),
% 0.21/0.48    inference(resolution,[],[f49,f95])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    r2_hidden(sK3,k1_xboole_0) | ~spl4_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f209])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    spl4_25 | ~spl4_9 | ~spl4_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f221,f217,f94,f224])).
% 0.21/0.48  fof(f224,plain,(
% 0.21/0.48    spl4_25 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    spl4_24 <=> v1_xboole_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | (~spl4_9 | ~spl4_24)),
% 0.21/0.48    inference(resolution,[],[f218,f103])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    v1_xboole_0(sK2) | ~spl4_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f217])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    spl4_24 | ~spl4_9 | ~spl4_22),
% 0.21/0.48    inference(avatar_split_clause,[],[f215,f205,f94,f217])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    spl4_22 <=> r2_hidden(sK2,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    v1_xboole_0(sK2) | (~spl4_9 | ~spl4_22)),
% 0.21/0.48    inference(resolution,[],[f206,f112])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    r2_hidden(sK2,k1_xboole_0) | ~spl4_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f205])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    spl4_23 | ~spl4_3 | ~spl4_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f194,f176,f70,f209])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl4_3 <=> r2_hidden(sK3,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    spl4_18 <=> k1_xboole_0 = sK0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    r2_hidden(sK3,k1_xboole_0) | (~spl4_3 | ~spl4_18)),
% 0.21/0.48    inference(superposition,[],[f71,f177])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | ~spl4_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f176])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    r2_hidden(sK3,sK0) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f70])).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    spl4_22 | ~spl4_4 | ~spl4_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f193,f176,f74,f205])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl4_4 <=> r2_hidden(sK2,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    r2_hidden(sK2,k1_xboole_0) | (~spl4_4 | ~spl4_18)),
% 0.21/0.48    inference(superposition,[],[f75,f177])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    r2_hidden(sK2,sK0) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    ~spl4_4 | spl4_1 | ~spl4_17 | ~spl4_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f186,f182,f173,f62,f74])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl4_1 <=> sK2 = sK3),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    spl4_17 <=> ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    spl4_19 <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    sK2 = sK3 | ~r2_hidden(sK2,sK0) | (~spl4_17 | ~spl4_19)),
% 0.21/0.48    inference(superposition,[],[f174,f183])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~spl4_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f182])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    ( ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,sK0)) ) | ~spl4_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f173])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    ~spl4_3 | spl4_19 | ~spl4_2 | ~spl4_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f179,f173,f66,f182,f70])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl4_2 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~r2_hidden(sK3,sK0) | (~spl4_2 | ~spl4_17)),
% 0.21/0.48    inference(superposition,[],[f174,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f66])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    ~spl4_6 | spl4_17 | spl4_18 | ~spl4_7 | ~spl4_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f170,f167,f86,f176,f173,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl4_6 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl4_7 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    spl4_16 <=> ! [X1,X0,X2] : (k1_xboole_0 = X0 | ~v1_funct_2(sK1,X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | (~spl4_7 | ~spl4_16)),
% 0.21/0.48    inference(resolution,[],[f168,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    v1_funct_2(sK1,sK0,sK0) | ~spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_2(sK1,X2,X0) | k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1) ) | ~spl4_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f167])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    ~spl4_8 | spl4_16 | ~spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f165,f78,f167,f90])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl4_8 <=> v1_funct_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl4_5 <=> v2_funct_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(sK1,X2,X0) | ~v1_funct_1(sK1)) ) | ~spl4_5),
% 0.21/0.48    inference(resolution,[],[f58,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    v2_funct_1(sK1) | ~spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f78])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v2_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f43,f94])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f90])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    v1_funct_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f30,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.49    inference(negated_conjecture,[],[f13])).
% 0.21/0.49  fof(f13,conjecture,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f36,f86])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f82])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f38,f78])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    v2_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f74])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    r2_hidden(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f40,f70])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    r2_hidden(sK3,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f41,f66])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ~spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f62])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    sK2 != sK3),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (9254)------------------------------
% 0.21/0.49  % (9254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9254)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (9254)Memory used [KB]: 10746
% 0.21/0.49  % (9254)Time elapsed: 0.060 s
% 0.21/0.49  % (9254)------------------------------
% 0.21/0.49  % (9254)------------------------------
% 0.21/0.49  % (9249)Refutation not found, incomplete strategy% (9249)------------------------------
% 0.21/0.49  % (9249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9249)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (9249)Memory used [KB]: 10618
% 0.21/0.49  % (9249)Time elapsed: 0.061 s
% 0.21/0.49  % (9249)------------------------------
% 0.21/0.49  % (9249)------------------------------
% 0.21/0.49  % (9244)Success in time 0.126 s
%------------------------------------------------------------------------------

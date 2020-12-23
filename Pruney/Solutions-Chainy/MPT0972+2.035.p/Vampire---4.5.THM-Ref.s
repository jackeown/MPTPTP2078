%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 281 expanded)
%              Number of leaves         :   39 ( 123 expanded)
%              Depth                    :    9
%              Number of atoms          :  483 (1035 expanded)
%              Number of equality atoms :  102 ( 194 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f464,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f92,f97,f102,f114,f119,f131,f136,f146,f155,f166,f173,f199,f203,f230,f236,f290,f297,f319,f393,f414,f446,f462,f463])).

fof(f463,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f462,plain,
    ( ~ spl8_10
    | ~ spl8_2
    | spl8_30
    | ~ spl8_20
    | ~ spl8_25
    | spl8_31 ),
    inference(avatar_split_clause,[],[f451,f443,f391,f233,f439,f74,f128])).

fof(f128,plain,
    ( spl8_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f74,plain,
    ( spl8_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f439,plain,
    ( spl8_30
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f233,plain,
    ( spl8_20
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f391,plain,
    ( spl8_25
  <=> ! [X0] :
        ( r2_hidden(sK4(sK3,X0),sK0)
        | sK3 = X0
        | k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f443,plain,
    ( spl8_31
  <=> r2_hidden(sK4(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f451,plain,
    ( sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_20
    | ~ spl8_25
    | spl8_31 ),
    inference(trivial_inequality_removal,[],[f450])).

fof(f450,plain,
    ( sK0 != sK0
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_20
    | ~ spl8_25
    | spl8_31 ),
    inference(forward_demodulation,[],[f447,f235])).

fof(f235,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f233])).

fof(f447,plain,
    ( sK2 = sK3
    | sK0 != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_25
    | spl8_31 ),
    inference(resolution,[],[f445,f392])).

fof(f392,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK3,X0),sK0)
        | sK3 = X0
        | k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f391])).

fof(f445,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),sK0)
    | spl8_31 ),
    inference(avatar_component_clause,[],[f443])).

fof(f446,plain,
    ( ~ spl8_10
    | ~ spl8_2
    | spl8_30
    | ~ spl8_31
    | ~ spl8_20
    | ~ spl8_29 ),
    inference(avatar_split_clause,[],[f437,f412,f233,f443,f439,f74,f128])).

fof(f412,plain,
    ( spl8_29
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ r2_hidden(sK4(sK3,X0),sK0)
        | sK3 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f437,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_20
    | ~ spl8_29 ),
    inference(trivial_inequality_removal,[],[f436])).

fof(f436,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_20
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f424,f235])).

fof(f424,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK0 != k1_relat_1(sK2)
    | ~ spl8_29 ),
    inference(equality_resolution,[],[f413])).

fof(f413,plain,
    ( ! [X0] :
        ( k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0))
        | ~ r2_hidden(sK4(sK3,X0),sK0)
        | sK3 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != sK0 )
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f412])).

fof(f414,plain,
    ( ~ spl8_8
    | spl8_29
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f387,f227,f412,f111])).

fof(f111,plain,
    ( spl8_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f227,plain,
    ( spl8_19
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f387,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK3)
        | sK3 = X0
        | ~ r2_hidden(sK4(sK3,X0),sK0) )
    | ~ spl8_19 ),
    inference(forward_demodulation,[],[f149,f229])).

fof(f229,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f227])).

fof(f149,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | ~ v1_relat_1(sK3)
      | sK3 = X0
      | ~ r2_hidden(sK4(sK3,X0),sK0) ) ),
    inference(global_subsumption,[],[f30,f147])).

fof(f147,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | ~ v1_relat_1(sK3)
      | sK3 = X0
      | ~ r2_hidden(sK4(sK3,X0),sK0) ) ),
    inference(superposition,[],[f40,f29])).

fof(f29,plain,(
    ! [X4] :
      ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

% (10402)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (10403)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f393,plain,
    ( ~ spl8_8
    | ~ spl8_1
    | spl8_25
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f231,f227,f391,f69,f111])).

fof(f69,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f231,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK3,X0),sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK3)
        | sK3 = X0 )
    | ~ spl8_19 ),
    inference(superposition,[],[f39,f229])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f319,plain,
    ( ~ spl8_24
    | spl8_5
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f318,f152,f144,f89,f294])).

fof(f294,plain,
    ( spl8_24
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f89,plain,
    ( spl8_5
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f144,plain,
    ( spl8_13
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f152,plain,
    ( spl8_14
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f318,plain,
    ( ~ v1_xboole_0(sK2)
    | spl8_5
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(resolution,[],[f308,f154])).

fof(f154,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f308,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X0)
        | ~ v1_xboole_0(X0) )
    | spl8_5
    | ~ spl8_13 ),
    inference(superposition,[],[f91,f301])).

fof(f301,plain,
    ( ! [X0] :
        ( sK3 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl8_13 ),
    inference(resolution,[],[f262,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f262,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(X0,sK3),X0)
        | sK3 = X0 )
    | ~ spl8_13 ),
    inference(resolution,[],[f145,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r2_hidden(sK6(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f145,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f144])).

fof(f91,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f297,plain,
    ( spl8_24
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f291,f288,f294])).

fof(f288,plain,
    ( spl8_23
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f291,plain,
    ( v1_xboole_0(sK2)
    | ~ spl8_23 ),
    inference(resolution,[],[f289,f41])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f289,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f288])).

fof(f290,plain,
    ( ~ spl8_12
    | spl8_23
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f156,f99,f288,f140])).

fof(f140,plain,
    ( spl8_12
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f99,plain,
    ( spl8_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl8_7 ),
    inference(resolution,[],[f126,f42])).

fof(f126,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X1,sK2) )
    | ~ spl8_7 ),
    inference(resolution,[],[f101,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f101,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f236,plain,
    ( ~ spl8_7
    | spl8_20
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f220,f170,f233,f99])).

fof(f170,plain,
    ( spl8_17
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f220,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_17 ),
    inference(superposition,[],[f172,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f172,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f170])).

fof(f230,plain,
    ( ~ spl8_6
    | spl8_19
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f167,f159,f227,f94])).

fof(f94,plain,
    ( spl8_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f159,plain,
    ( spl8_15
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f167,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_15 ),
    inference(superposition,[],[f161,f50])).

fof(f161,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f203,plain,(
    spl8_18 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl8_18 ),
    inference(unit_resulting_resolution,[],[f37,f198])).

fof(f198,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl8_18 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl8_18
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f199,plain,
    ( ~ spl8_18
    | spl8_12
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f194,f163,f140,f196])).

fof(f163,plain,
    ( spl8_16
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f194,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl8_12
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f185,f59])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f185,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
    | spl8_12
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f142,f165])).

fof(f165,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f142,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f173,plain,
    ( ~ spl8_4
    | spl8_17
    | spl8_16
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f121,f99,f163,f170,f84])).

fof(f84,plain,
    ( spl8_4
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f121,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl8_7 ),
    inference(resolution,[],[f101,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f166,plain,
    ( ~ spl8_3
    | spl8_15
    | spl8_16
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f104,f94,f163,f159,f79])).

fof(f79,plain,
    ( spl8_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f104,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_6 ),
    inference(resolution,[],[f96,f56])).

fof(f96,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f155,plain,
    ( spl8_9
    | spl8_14
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f123,f99,f152,f116])).

fof(f116,plain,
    ( spl8_9
  <=> sP7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f123,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | sP7(sK1,sK0)
    | ~ spl8_7 ),
    inference(resolution,[],[f101,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP7(X1,X0) ) ),
    inference(cnf_transformation,[],[f66_D])).

fof(f66_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP7(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f146,plain,
    ( ~ spl8_12
    | spl8_13
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f137,f94,f144,f140])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl8_6 ),
    inference(resolution,[],[f109,f42])).

fof(f109,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X1,sK3) )
    | ~ spl8_6 ),
    inference(resolution,[],[f96,f43])).

fof(f136,plain,
    ( spl8_9
    | spl8_11
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f106,f94,f133,f116])).

fof(f133,plain,
    ( spl8_11
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f106,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | sP7(sK1,sK0)
    | ~ spl8_6 ),
    inference(resolution,[],[f96,f66])).

fof(f131,plain,
    ( spl8_10
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f122,f99,f128])).

fof(f122,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_7 ),
    inference(resolution,[],[f101,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f119,plain,
    ( ~ spl8_9
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f107,f94,f116])).

fof(f107,plain,
    ( ~ sP7(sK1,sK0)
    | ~ spl8_6 ),
    inference(resolution,[],[f96,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP7(X1,X0) ) ),
    inference(general_splitting,[],[f58,f66_D])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f114,plain,
    ( spl8_8
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f105,f94,f111])).

fof(f105,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_6 ),
    inference(resolution,[],[f96,f49])).

fof(f102,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f36,f99])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f97,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f32,f94])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f92,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f33,f89])).

fof(f33,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f87,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f35,f84])).

fof(f35,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f31,f79])).

fof(f31,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f34,f74])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f30,f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (10400)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.50  % (10392)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (10407)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (10388)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (10387)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (10399)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (10389)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (10384)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (10406)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (10412)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (10398)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (10408)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (10391)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (10404)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (10385)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (10390)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (10393)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (10386)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (10395)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (10396)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (10394)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (10410)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (10413)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (10409)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (10405)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (10411)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (10401)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (10397)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (10406)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f464,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f92,f97,f102,f114,f119,f131,f136,f146,f155,f166,f173,f199,f203,f230,f236,f290,f297,f319,f393,f414,f446,f462,f463])).
% 0.20/0.54  fof(f463,plain,(
% 0.20/0.54    sK2 != sK3 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.20/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.54  fof(f462,plain,(
% 0.20/0.54    ~spl8_10 | ~spl8_2 | spl8_30 | ~spl8_20 | ~spl8_25 | spl8_31),
% 0.20/0.54    inference(avatar_split_clause,[],[f451,f443,f391,f233,f439,f74,f128])).
% 0.20/0.54  fof(f128,plain,(
% 0.20/0.54    spl8_10 <=> v1_relat_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    spl8_2 <=> v1_funct_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.54  fof(f439,plain,(
% 0.20/0.54    spl8_30 <=> sK2 = sK3),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.20/0.54  fof(f233,plain,(
% 0.20/0.54    spl8_20 <=> sK0 = k1_relat_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.20/0.54  fof(f391,plain,(
% 0.20/0.54    spl8_25 <=> ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.20/0.54  fof(f443,plain,(
% 0.20/0.54    spl8_31 <=> r2_hidden(sK4(sK3,sK2),sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.20/0.54  fof(f451,plain,(
% 0.20/0.54    sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl8_20 | ~spl8_25 | spl8_31)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f450])).
% 0.20/0.54  fof(f450,plain,(
% 0.20/0.54    sK0 != sK0 | sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl8_20 | ~spl8_25 | spl8_31)),
% 0.20/0.54    inference(forward_demodulation,[],[f447,f235])).
% 0.20/0.54  fof(f235,plain,(
% 0.20/0.54    sK0 = k1_relat_1(sK2) | ~spl8_20),
% 0.20/0.54    inference(avatar_component_clause,[],[f233])).
% 0.20/0.54  fof(f447,plain,(
% 0.20/0.54    sK2 = sK3 | sK0 != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl8_25 | spl8_31)),
% 0.20/0.54    inference(resolution,[],[f445,f392])).
% 0.20/0.54  fof(f392,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl8_25),
% 0.20/0.54    inference(avatar_component_clause,[],[f391])).
% 0.20/0.54  fof(f445,plain,(
% 0.20/0.54    ~r2_hidden(sK4(sK3,sK2),sK0) | spl8_31),
% 0.20/0.54    inference(avatar_component_clause,[],[f443])).
% 0.20/0.54  fof(f446,plain,(
% 0.20/0.54    ~spl8_10 | ~spl8_2 | spl8_30 | ~spl8_31 | ~spl8_20 | ~spl8_29),
% 0.20/0.54    inference(avatar_split_clause,[],[f437,f412,f233,f443,f439,f74,f128])).
% 0.20/0.54  fof(f412,plain,(
% 0.20/0.54    spl8_29 <=> ! [X0] : (k1_relat_1(X0) != sK0 | ~r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.20/0.54  fof(f437,plain,(
% 0.20/0.54    ~r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl8_20 | ~spl8_29)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f436])).
% 0.20/0.54  fof(f436,plain,(
% 0.20/0.54    sK0 != sK0 | ~r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl8_20 | ~spl8_29)),
% 0.20/0.54    inference(forward_demodulation,[],[f424,f235])).
% 0.20/0.54  fof(f424,plain,(
% 0.20/0.54    ~r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK0 != k1_relat_1(sK2) | ~spl8_29),
% 0.20/0.54    inference(equality_resolution,[],[f413])).
% 0.20/0.54  fof(f413,plain,(
% 0.20/0.54    ( ! [X0] : (k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)) | ~r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != sK0) ) | ~spl8_29),
% 0.20/0.54    inference(avatar_component_clause,[],[f412])).
% 0.20/0.54  fof(f414,plain,(
% 0.20/0.54    ~spl8_8 | spl8_29 | ~spl8_19),
% 0.20/0.54    inference(avatar_split_clause,[],[f387,f227,f412,f111])).
% 0.20/0.54  fof(f111,plain,(
% 0.20/0.54    spl8_8 <=> v1_relat_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.54  fof(f227,plain,(
% 0.20/0.54    spl8_19 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.20/0.54  fof(f387,plain,(
% 0.20/0.54    ( ! [X0] : (k1_relat_1(X0) != sK0 | k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK3) | sK3 = X0 | ~r2_hidden(sK4(sK3,X0),sK0)) ) | ~spl8_19),
% 0.20/0.54    inference(forward_demodulation,[],[f149,f229])).
% 0.20/0.54  fof(f229,plain,(
% 0.20/0.54    sK0 = k1_relat_1(sK3) | ~spl8_19),
% 0.20/0.54    inference(avatar_component_clause,[],[f227])).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    ( ! [X0] : (k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK3 = X0 | ~r2_hidden(sK4(sK3,X0),sK0)) )),
% 0.20/0.54    inference(global_subsumption,[],[f30,f147])).
% 0.20/0.54  fof(f147,plain,(
% 0.20/0.54    ( ! [X0] : (k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)) | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK3 = X0 | ~r2_hidden(sK4(sK3,X0),sK0)) )),
% 0.20/0.54    inference(superposition,[],[f40,f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ( ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.54    inference(flattening,[],[f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.54    inference(negated_conjecture,[],[f13])).
% 0.20/0.54  % (10402)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (10403)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  fof(f13,conjecture,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | X0 = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(flattening,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    v1_funct_1(sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f393,plain,(
% 0.20/0.55    ~spl8_8 | ~spl8_1 | spl8_25 | ~spl8_19),
% 0.20/0.55    inference(avatar_split_clause,[],[f231,f227,f391,f69,f111])).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    spl8_1 <=> v1_funct_1(sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.55  fof(f231,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | ~v1_relat_1(sK3) | sK3 = X0) ) | ~spl8_19),
% 0.20/0.55    inference(superposition,[],[f39,f229])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | X0 = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f319,plain,(
% 0.20/0.55    ~spl8_24 | spl8_5 | ~spl8_13 | ~spl8_14),
% 0.20/0.55    inference(avatar_split_clause,[],[f318,f152,f144,f89,f294])).
% 0.20/0.55  fof(f294,plain,(
% 0.20/0.55    spl8_24 <=> v1_xboole_0(sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    spl8_5 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.55  fof(f144,plain,(
% 0.20/0.55    spl8_13 <=> ! [X0] : ~r2_hidden(X0,sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.55  fof(f152,plain,(
% 0.20/0.55    spl8_14 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.55  fof(f318,plain,(
% 0.20/0.55    ~v1_xboole_0(sK2) | (spl8_5 | ~spl8_13 | ~spl8_14)),
% 0.20/0.55    inference(resolution,[],[f308,f154])).
% 0.20/0.55  fof(f154,plain,(
% 0.20/0.55    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl8_14),
% 0.20/0.55    inference(avatar_component_clause,[],[f152])).
% 0.20/0.55  fof(f308,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_relset_1(sK0,sK1,sK2,X0) | ~v1_xboole_0(X0)) ) | (spl8_5 | ~spl8_13)),
% 0.20/0.55    inference(superposition,[],[f91,f301])).
% 0.20/0.55  fof(f301,plain,(
% 0.20/0.55    ( ! [X0] : (sK3 = X0 | ~v1_xboole_0(X0)) ) | ~spl8_13),
% 0.20/0.55    inference(resolution,[],[f262,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.55  fof(f262,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(sK6(X0,sK3),X0) | sK3 = X0) ) | ~spl8_13),
% 0.20/0.55    inference(resolution,[],[f145,f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | r2_hidden(sK6(X0,X1),X0) | X0 = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.20/0.55  fof(f145,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl8_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f144])).
% 0.20/0.55  fof(f91,plain,(
% 0.20/0.55    ~r2_relset_1(sK0,sK1,sK2,sK3) | spl8_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f89])).
% 0.20/0.55  fof(f297,plain,(
% 0.20/0.55    spl8_24 | ~spl8_23),
% 0.20/0.55    inference(avatar_split_clause,[],[f291,f288,f294])).
% 0.20/0.55  fof(f288,plain,(
% 0.20/0.55    spl8_23 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.20/0.55  fof(f291,plain,(
% 0.20/0.55    v1_xboole_0(sK2) | ~spl8_23),
% 0.20/0.55    inference(resolution,[],[f289,f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f1])).
% 0.20/0.55  fof(f289,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl8_23),
% 0.20/0.55    inference(avatar_component_clause,[],[f288])).
% 0.20/0.55  fof(f290,plain,(
% 0.20/0.55    ~spl8_12 | spl8_23 | ~spl8_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f156,f99,f288,f140])).
% 0.20/0.55  fof(f140,plain,(
% 0.20/0.55    spl8_12 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    spl8_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.55  fof(f156,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))) ) | ~spl8_7),
% 0.20/0.55    inference(resolution,[],[f126,f42])).
% 0.20/0.55  fof(f126,plain,(
% 0.20/0.55    ( ! [X1] : (r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X1,sK2)) ) | ~spl8_7),
% 0.20/0.55    inference(resolution,[],[f101,f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.55  fof(f101,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f99])).
% 0.20/0.55  fof(f236,plain,(
% 0.20/0.55    ~spl8_7 | spl8_20 | ~spl8_17),
% 0.20/0.55    inference(avatar_split_clause,[],[f220,f170,f233,f99])).
% 0.20/0.55  fof(f170,plain,(
% 0.20/0.55    spl8_17 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.20/0.55  fof(f220,plain,(
% 0.20/0.55    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_17),
% 0.20/0.55    inference(superposition,[],[f172,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.55  fof(f172,plain,(
% 0.20/0.55    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl8_17),
% 0.20/0.55    inference(avatar_component_clause,[],[f170])).
% 0.20/0.55  fof(f230,plain,(
% 0.20/0.55    ~spl8_6 | spl8_19 | ~spl8_15),
% 0.20/0.55    inference(avatar_split_clause,[],[f167,f159,f227,f94])).
% 0.20/0.55  fof(f94,plain,(
% 0.20/0.55    spl8_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.55  fof(f159,plain,(
% 0.20/0.55    spl8_15 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.20/0.55  fof(f167,plain,(
% 0.20/0.55    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_15),
% 0.20/0.55    inference(superposition,[],[f161,f50])).
% 0.20/0.55  fof(f161,plain,(
% 0.20/0.55    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl8_15),
% 0.20/0.55    inference(avatar_component_clause,[],[f159])).
% 0.20/0.55  fof(f203,plain,(
% 0.20/0.55    spl8_18),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f200])).
% 0.20/0.55  fof(f200,plain,(
% 0.20/0.55    $false | spl8_18),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f37,f198])).
% 0.20/0.55  fof(f198,plain,(
% 0.20/0.55    ~v1_xboole_0(k1_xboole_0) | spl8_18),
% 0.20/0.55    inference(avatar_component_clause,[],[f196])).
% 0.20/0.55  fof(f196,plain,(
% 0.20/0.55    spl8_18 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    v1_xboole_0(k1_xboole_0)),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    v1_xboole_0(k1_xboole_0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.55  fof(f199,plain,(
% 0.20/0.55    ~spl8_18 | spl8_12 | ~spl8_16),
% 0.20/0.55    inference(avatar_split_clause,[],[f194,f163,f140,f196])).
% 0.20/0.55  fof(f163,plain,(
% 0.20/0.55    spl8_16 <=> k1_xboole_0 = sK1),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.20/0.55  fof(f194,plain,(
% 0.20/0.55    ~v1_xboole_0(k1_xboole_0) | (spl8_12 | ~spl8_16)),
% 0.20/0.55    inference(forward_demodulation,[],[f185,f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.55  fof(f185,plain,(
% 0.20/0.55    ~v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) | (spl8_12 | ~spl8_16)),
% 0.20/0.55    inference(backward_demodulation,[],[f142,f165])).
% 0.20/0.55  fof(f165,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | ~spl8_16),
% 0.20/0.55    inference(avatar_component_clause,[],[f163])).
% 0.20/0.55  fof(f142,plain,(
% 0.20/0.55    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl8_12),
% 0.20/0.55    inference(avatar_component_clause,[],[f140])).
% 0.20/0.55  fof(f173,plain,(
% 0.20/0.55    ~spl8_4 | spl8_17 | spl8_16 | ~spl8_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f121,f99,f163,f170,f84])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    spl8_4 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.55  fof(f121,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl8_7),
% 0.20/0.55    inference(resolution,[],[f101,f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(flattening,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.55  fof(f166,plain,(
% 0.20/0.55    ~spl8_3 | spl8_15 | spl8_16 | ~spl8_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f104,f94,f163,f159,f79])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    spl8_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.55  fof(f104,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl8_6),
% 0.20/0.55    inference(resolution,[],[f96,f56])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f94])).
% 0.20/0.55  fof(f155,plain,(
% 0.20/0.55    spl8_9 | spl8_14 | ~spl8_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f123,f99,f152,f116])).
% 0.20/0.55  fof(f116,plain,(
% 0.20/0.55    spl8_9 <=> sP7(sK1,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    r2_relset_1(sK0,sK1,sK2,sK2) | sP7(sK1,sK0) | ~spl8_7),
% 0.20/0.55    inference(resolution,[],[f101,f66])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2) | sP7(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f66_D])).
% 0.20/0.55  fof(f66_D,plain,(
% 0.20/0.55    ( ! [X0,X1] : (( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) <=> ~sP7(X1,X0)) )),
% 0.20/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 0.20/0.55  fof(f146,plain,(
% 0.20/0.55    ~spl8_12 | spl8_13 | ~spl8_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f137,f94,f144,f140])).
% 0.20/0.55  fof(f137,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,sK3) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))) ) | ~spl8_6),
% 0.20/0.55    inference(resolution,[],[f109,f42])).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    ( ! [X1] : (r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X1,sK3)) ) | ~spl8_6),
% 0.20/0.55    inference(resolution,[],[f96,f43])).
% 0.20/0.55  fof(f136,plain,(
% 0.20/0.55    spl8_9 | spl8_11 | ~spl8_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f106,f94,f133,f116])).
% 0.20/0.55  fof(f133,plain,(
% 0.20/0.55    spl8_11 <=> r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    r2_relset_1(sK0,sK1,sK3,sK3) | sP7(sK1,sK0) | ~spl8_6),
% 0.20/0.55    inference(resolution,[],[f96,f66])).
% 0.20/0.55  fof(f131,plain,(
% 0.20/0.55    spl8_10 | ~spl8_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f122,f99,f128])).
% 0.20/0.55  fof(f122,plain,(
% 0.20/0.55    v1_relat_1(sK2) | ~spl8_7),
% 0.20/0.55    inference(resolution,[],[f101,f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.55  fof(f119,plain,(
% 0.20/0.55    ~spl8_9 | ~spl8_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f107,f94,f116])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    ~sP7(sK1,sK0) | ~spl8_6),
% 0.20/0.55    inference(resolution,[],[f96,f67])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP7(X1,X0)) )),
% 0.20/0.55    inference(general_splitting,[],[f58,f66_D])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(flattening,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    spl8_8 | ~spl8_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f105,f94,f111])).
% 0.20/0.55  fof(f105,plain,(
% 0.20/0.55    v1_relat_1(sK3) | ~spl8_6),
% 0.20/0.55    inference(resolution,[],[f96,f49])).
% 0.20/0.55  fof(f102,plain,(
% 0.20/0.55    spl8_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f36,f99])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    spl8_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f32,f94])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    ~spl8_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f33,f89])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f87,plain,(
% 0.20/0.55    spl8_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f35,f84])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    spl8_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f31,f79])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    spl8_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f34,f74])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    v1_funct_1(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    spl8_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f30,f69])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (10406)------------------------------
% 0.20/0.55  % (10406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (10406)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (10406)Memory used [KB]: 11001
% 0.20/0.55  % (10406)Time elapsed: 0.084 s
% 0.20/0.55  % (10406)------------------------------
% 0.20/0.55  % (10406)------------------------------
% 0.20/0.55  % (10383)Success in time 0.196 s
%------------------------------------------------------------------------------

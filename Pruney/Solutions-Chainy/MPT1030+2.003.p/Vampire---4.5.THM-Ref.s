%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 136 expanded)
%              Number of leaves         :   17 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  220 ( 400 expanded)
%              Number of equality atoms :   27 (  72 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f35,f44,f49,f54,f60,f66,f74,f78,f109,f117,f129,f138])).

fof(f138,plain,
    ( ~ spl3_12
    | spl3_13
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl3_12
    | spl3_13
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f136,f116])).

fof(f116,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl3_13
  <=> v1_partfun1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f136,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(resolution,[],[f110,f128])).

fof(f128,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl3_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_partfun1(X0,k1_xboole_0) )
    | ~ spl3_12 ),
    inference(resolution,[],[f108,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f108,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_12
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f129,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f96,f46,f41,f37,f126])).

fof(f37,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f41,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f46,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f96,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f92,f39])).

fof(f39,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f92,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f48,f42])).

fof(f42,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f48,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f117,plain,
    ( ~ spl3_13
    | ~ spl3_3
    | spl3_8 ),
    inference(avatar_split_clause,[],[f87,f63,f37,f114])).

fof(f63,plain,
    ( spl3_8
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f87,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | ~ spl3_3
    | spl3_8 ),
    inference(superposition,[],[f65,f39])).

fof(f65,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f109,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f89,f71,f41,f106])).

fof(f71,plain,
    ( spl3_9
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f89,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(superposition,[],[f73,f42])).

fof(f73,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f78,plain,
    ( spl3_4
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl3_4
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f76,f43])).

fof(f43,plain,
    ( k1_xboole_0 != sK1
    | spl3_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f76,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_9 ),
    inference(resolution,[],[f73,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f74,plain,
    ( spl3_9
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | spl3_8 ),
    inference(avatar_split_clause,[],[f69,f63,f46,f32,f25,f71])).

fof(f25,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f32,plain,
    ( spl3_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f69,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | spl3_8 ),
    inference(subsumption_resolution,[],[f68,f34])).

fof(f34,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f68,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | v1_xboole_0(sK1)
    | ~ spl3_1
    | ~ spl3_5
    | spl3_8 ),
    inference(resolution,[],[f67,f48])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK2,sK0,X0)
        | v1_xboole_0(X0) )
    | ~ spl3_1
    | spl3_8 ),
    inference(resolution,[],[f65,f30])).

fof(f30,plain,
    ( ! [X2,X3] :
        ( v1_partfun1(sK2,X2)
        | v1_xboole_0(X3)
        | ~ v1_funct_2(sK2,X2,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f27,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f27,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f66,plain,
    ( ~ spl3_8
    | spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f61,f57,f51,f63])).

fof(f51,plain,
    ( spl3_6
  <=> v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f57,plain,
    ( spl3_7
  <=> sK2 = k3_partfun1(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f61,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | spl3_6
    | ~ spl3_7 ),
    inference(superposition,[],[f53,f59])).

fof(f59,plain,
    ( sK2 = k3_partfun1(sK2,sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f53,plain,
    ( ~ v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f60,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f55,f46,f25,f57])).

fof(f55,plain,
    ( sK2 = k3_partfun1(sK2,sK0,sK1)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(resolution,[],[f29,f48])).

fof(f29,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | sK2 = k3_partfun1(sK2,X0,X1) )
    | ~ spl3_1 ),
    inference(resolution,[],[f27,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_partfun1(X2,X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k3_partfun1(X2,X0,X1) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_partfun1)).

fof(f54,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f19,f51])).

fof(f19,plain,(
    ~ v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(k3_partfun1(X2,X0,X1),X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => v1_partfun1(k3_partfun1(X2,X0,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => v1_partfun1(k3_partfun1(X2,X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_funct_2)).

fof(f49,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f46])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f8])).

fof(f44,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f15,f41,f37])).

fof(f15,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f32])).

fof(f17,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f28,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f16,f25])).

fof(f16,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:44:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.46  % (28859)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.47  % (28852)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (28847)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (28853)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (28847)Refutation not found, incomplete strategy% (28847)------------------------------
% 0.22/0.48  % (28847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (28847)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (28847)Memory used [KB]: 10618
% 0.22/0.48  % (28847)Time elapsed: 0.047 s
% 0.22/0.48  % (28847)------------------------------
% 0.22/0.48  % (28847)------------------------------
% 0.22/0.48  % (28857)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (28857)Refutation not found, incomplete strategy% (28857)------------------------------
% 0.22/0.49  % (28857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (28857)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (28857)Memory used [KB]: 6140
% 0.22/0.49  % (28857)Time elapsed: 0.053 s
% 0.22/0.49  % (28857)------------------------------
% 0.22/0.49  % (28857)------------------------------
% 0.22/0.49  % (28848)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (28848)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f28,f35,f44,f49,f54,f60,f66,f74,f78,f109,f117,f129,f138])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    ~spl3_12 | spl3_13 | ~spl3_15),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f137])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    $false | (~spl3_12 | spl3_13 | ~spl3_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f136,f116])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    ~v1_partfun1(sK2,k1_xboole_0) | spl3_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f114])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    spl3_13 <=> v1_partfun1(sK2,k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    v1_partfun1(sK2,k1_xboole_0) | (~spl3_12 | ~spl3_15)),
% 0.22/0.49    inference(resolution,[],[f110,f128])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f126])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    spl3_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X0,k1_xboole_0)) ) | ~spl3_12),
% 0.22/0.49    inference(resolution,[],[f108,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0) | ~spl3_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f106])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    spl3_12 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    spl3_15 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f96,f46,f41,f37,f126])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    spl3_3 <=> k1_xboole_0 = sK0),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    spl3_4 <=> k1_xboole_0 = sK1),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.22/0.49    inference(forward_demodulation,[],[f92,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    k1_xboole_0 = sK0 | ~spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f37])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl3_4 | ~spl3_5)),
% 0.22/0.49    inference(superposition,[],[f48,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | ~spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f41])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f46])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    ~spl3_13 | ~spl3_3 | spl3_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f87,f63,f37,f114])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    spl3_8 <=> v1_partfun1(sK2,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ~v1_partfun1(sK2,k1_xboole_0) | (~spl3_3 | spl3_8)),
% 0.22/0.49    inference(superposition,[],[f65,f39])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ~v1_partfun1(sK2,sK0) | spl3_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f63])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    spl3_12 | ~spl3_4 | ~spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f89,f71,f41,f106])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl3_9 <=> v1_xboole_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0) | (~spl3_4 | ~spl3_9)),
% 0.22/0.49    inference(superposition,[],[f73,f42])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    v1_xboole_0(sK1) | ~spl3_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f71])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    spl3_4 | ~spl3_9),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    $false | (spl3_4 | ~spl3_9)),
% 0.22/0.49    inference(subsumption_resolution,[],[f76,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    k1_xboole_0 != sK1 | spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f41])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | ~spl3_9),
% 0.22/0.49    inference(resolution,[],[f73,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    spl3_9 | ~spl3_1 | ~spl3_2 | ~spl3_5 | spl3_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f69,f63,f46,f32,f25,f71])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    spl3_1 <=> v1_funct_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    spl3_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    v1_xboole_0(sK1) | (~spl3_1 | ~spl3_2 | ~spl3_5 | spl3_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f68,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    v1_funct_2(sK2,sK0,sK1) | ~spl3_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f32])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,sK0,sK1) | v1_xboole_0(sK1) | (~spl3_1 | ~spl3_5 | spl3_8)),
% 0.22/0.49    inference(resolution,[],[f67,f48])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_2(sK2,sK0,X0) | v1_xboole_0(X0)) ) | (~spl3_1 | spl3_8)),
% 0.22/0.49    inference(resolution,[],[f65,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X2,X3] : (v1_partfun1(sK2,X2) | v1_xboole_0(X3) | ~v1_funct_2(sK2,X2,X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl3_1),
% 0.22/0.49    inference(resolution,[],[f27,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.49    inference(flattening,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    v1_funct_1(sK2) | ~spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f25])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ~spl3_8 | spl3_6 | ~spl3_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f61,f57,f51,f63])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    spl3_6 <=> v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    spl3_7 <=> sK2 = k3_partfun1(sK2,sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ~v1_partfun1(sK2,sK0) | (spl3_6 | ~spl3_7)),
% 0.22/0.49    inference(superposition,[],[f53,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    sK2 = k3_partfun1(sK2,sK0,sK1) | ~spl3_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f57])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ~v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0) | spl3_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f51])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl3_7 | ~spl3_1 | ~spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f55,f46,f25,f57])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    sK2 = k3_partfun1(sK2,sK0,sK1) | (~spl3_1 | ~spl3_5)),
% 0.22/0.49    inference(resolution,[],[f29,f48])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 = k3_partfun1(sK2,X0,X1)) ) | ~spl3_1),
% 0.22/0.49    inference(resolution,[],[f27,f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_partfun1(X2,X0,X1) = X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k3_partfun1(X2,X0,X1) = X2)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_partfun1)).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ~spl3_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f19,f51])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ~v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (~v1_partfun1(k3_partfun1(X2,X0,X1),X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.49    inference(flattening,[],[f7])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((~v1_partfun1(k3_partfun1(X2,X0,X1),X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => v1_partfun1(k3_partfun1(X2,X0,X1),X0)))),
% 0.22/0.49    inference(negated_conjecture,[],[f5])).
% 0.22/0.49  fof(f5,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => v1_partfun1(k3_partfun1(X2,X0,X1),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_funct_2)).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f18,f46])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    spl3_3 | ~spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f15,f41,f37])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f17,f32])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f16,f25])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    v1_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (28848)------------------------------
% 0.22/0.49  % (28848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (28848)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (28848)Memory used [KB]: 10618
% 0.22/0.49  % (28848)Time elapsed: 0.060 s
% 0.22/0.49  % (28848)------------------------------
% 0.22/0.49  % (28848)------------------------------
% 0.22/0.49  % (28839)Success in time 0.124 s
%------------------------------------------------------------------------------

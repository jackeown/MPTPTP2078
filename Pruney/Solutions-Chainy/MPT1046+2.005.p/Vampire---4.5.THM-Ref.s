%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 126 expanded)
%              Number of leaves         :   16 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  217 ( 373 expanded)
%              Number of equality atoms :   37 (  63 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f36,f41,f46,f53,f63,f71,f87,f96,f101,f102,f114])).

fof(f114,plain,
    ( ~ spl2_1
    | spl2_10
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl2_1
    | spl2_10
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f112,f95])).

fof(f95,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl2_11
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f112,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_1
    | spl2_10
    | ~ spl2_12 ),
    inference(resolution,[],[f91,f100])).

fof(f100,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl2_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f91,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ v1_funct_2(sK1,k1_xboole_0,X1) )
    | ~ spl2_1
    | spl2_10 ),
    inference(subsumption_resolution,[],[f90,f27])).

fof(f27,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl2_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f90,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK1,k1_xboole_0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ v1_funct_1(sK1) )
    | spl2_10 ),
    inference(resolution,[],[f86,f23])).

fof(f23,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f86,plain,
    ( ~ v1_partfun1(sK1,k1_xboole_0)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_10
  <=> v1_partfun1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f102,plain,
    ( sK1 != k3_partfun1(sK1,sK0,sK0)
    | k1_tarski(sK1) != k5_partfun1(sK0,sK0,sK1)
    | k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_tarski(sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f101,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f77,f68,f38,f98])).

fof(f38,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f68,plain,
    ( spl2_8
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f77,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(superposition,[],[f40,f70])).

fof(f70,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f40,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f96,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f76,f68,f33,f93])).

fof(f33,plain,
    ( spl2_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f76,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(superposition,[],[f35,f70])).

fof(f35,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f87,plain,
    ( ~ spl2_10
    | spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f80,f68,f56,f84])).

fof(f56,plain,
    ( spl2_6
  <=> v1_partfun1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f80,plain,
    ( ~ v1_partfun1(sK1,k1_xboole_0)
    | spl2_6
    | ~ spl2_8 ),
    inference(superposition,[],[f58,f70])).

fof(f58,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f71,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_6 ),
    inference(avatar_split_clause,[],[f66,f56,f38,f33,f25,f68])).

fof(f66,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_6 ),
    inference(subsumption_resolution,[],[f65,f35])).

fof(f65,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_1
    | ~ spl2_3
    | spl2_6 ),
    inference(resolution,[],[f64,f40])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | k1_xboole_0 = X0
        | ~ v1_funct_2(sK1,sK0,X0) )
    | ~ spl2_1
    | spl2_6 ),
    inference(resolution,[],[f58,f30])).

fof(f30,plain,
    ( ! [X2,X3] :
        ( v1_partfun1(sK1,X2)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k1_xboole_0 = X3
        | ~ v1_funct_2(sK1,X2,X3) )
    | ~ spl2_1 ),
    inference(resolution,[],[f27,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f63,plain,
    ( ~ spl2_6
    | spl2_7
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f48,f38,f25,f60,f56])).

fof(f60,plain,
    ( spl2_7
  <=> k1_tarski(sK1) = k5_partfun1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f48,plain,
    ( k1_tarski(sK1) = k5_partfun1(sK0,sK0,sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(resolution,[],[f29,f40])).

fof(f29,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_tarski(sK1) = k5_partfun1(X0,X1,sK1)
        | ~ v1_partfun1(sK1,X0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f27,f22])).

% (9586)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_partfun1(X0,X1,X2) = k1_tarski(X2)
      | ~ v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_partfun1)).

fof(f53,plain,
    ( spl2_5
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f47,f38,f25,f50])).

fof(f50,plain,
    ( spl2_5
  <=> sK1 = k3_partfun1(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f47,plain,
    ( sK1 = k3_partfun1(sK1,sK0,sK0)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(resolution,[],[f31,f40])).

fof(f31,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | sK1 = k3_partfun1(sK1,X4,X5) )
    | ~ spl2_1 ),
    inference(resolution,[],[f27,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_partfun1(X2,X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k3_partfun1(X2,X0,X1) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_partfun1)).

fof(f46,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f17,f43])).

fof(f43,plain,
    ( spl2_4
  <=> k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f17,plain,(
    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_2)).

fof(f41,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f16,f38])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f36,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f15,f33])).

fof(f15,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f28,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f14,f25])).

fof(f14,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (9591)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.46  % (9591)Refutation not found, incomplete strategy% (9591)------------------------------
% 0.20/0.46  % (9591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (9591)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (9591)Memory used [KB]: 6140
% 0.20/0.46  % (9591)Time elapsed: 0.056 s
% 0.20/0.46  % (9591)------------------------------
% 0.20/0.46  % (9591)------------------------------
% 0.20/0.46  % (9584)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (9584)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f28,f36,f41,f46,f53,f63,f71,f87,f96,f101,f102,f114])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    ~spl2_1 | spl2_10 | ~spl2_11 | ~spl2_12),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f113])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    $false | (~spl2_1 | spl2_10 | ~spl2_11 | ~spl2_12)),
% 0.20/0.47    inference(subsumption_resolution,[],[f112,f95])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~spl2_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f93])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    spl2_11 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl2_1 | spl2_10 | ~spl2_12)),
% 0.20/0.47    inference(resolution,[],[f91,f100])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl2_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f98])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    spl2_12 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(sK1,k1_xboole_0,X1)) ) | (~spl2_1 | spl2_10)),
% 0.20/0.47    inference(subsumption_resolution,[],[f90,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    v1_funct_1(sK1) | ~spl2_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    spl2_1 <=> v1_funct_1(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ( ! [X1] : (~v1_funct_2(sK1,k1_xboole_0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(sK1)) ) | spl2_10),
% 0.20/0.47    inference(resolution,[],[f86,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.47    inference(equality_resolution,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | v1_partfun1(X2,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    ~v1_partfun1(sK1,k1_xboole_0) | spl2_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f84])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    spl2_10 <=> v1_partfun1(sK1,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    sK1 != k3_partfun1(sK1,sK0,sK0) | k1_tarski(sK1) != k5_partfun1(sK0,sK0,sK1) | k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_tarski(sK1)),
% 0.20/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    spl2_12 | ~spl2_3 | ~spl2_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f77,f68,f38,f98])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl2_8 <=> k1_xboole_0 = sK0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl2_3 | ~spl2_8)),
% 0.20/0.47    inference(superposition,[],[f40,f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | ~spl2_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f68])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f38])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    spl2_11 | ~spl2_2 | ~spl2_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f76,f68,f33,f93])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    spl2_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl2_2 | ~spl2_8)),
% 0.20/0.47    inference(superposition,[],[f35,f70])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    v1_funct_2(sK1,sK0,sK0) | ~spl2_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f33])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    ~spl2_10 | spl2_6 | ~spl2_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f80,f68,f56,f84])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    spl2_6 <=> v1_partfun1(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    ~v1_partfun1(sK1,k1_xboole_0) | (spl2_6 | ~spl2_8)),
% 0.20/0.47    inference(superposition,[],[f58,f70])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ~v1_partfun1(sK1,sK0) | spl2_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f56])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl2_8 | ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f66,f56,f38,f33,f25,f68])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_6)),
% 0.20/0.47    inference(subsumption_resolution,[],[f65,f35])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | (~spl2_1 | ~spl2_3 | spl2_6)),
% 0.20/0.47    inference(resolution,[],[f64,f40])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = X0 | ~v1_funct_2(sK1,sK0,X0)) ) | (~spl2_1 | spl2_6)),
% 0.20/0.47    inference(resolution,[],[f58,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X2,X3] : (v1_partfun1(sK1,X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = X3 | ~v1_funct_2(sK1,X2,X3)) ) | ~spl2_1),
% 0.20/0.47    inference(resolution,[],[f27,f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ~spl2_6 | spl2_7 | ~spl2_1 | ~spl2_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f48,f38,f25,f60,f56])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    spl2_7 <=> k1_tarski(sK1) = k5_partfun1(sK0,sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    k1_tarski(sK1) = k5_partfun1(sK0,sK0,sK1) | ~v1_partfun1(sK1,sK0) | (~spl2_1 | ~spl2_3)),
% 0.20/0.47    inference(resolution,[],[f29,f40])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_tarski(sK1) = k5_partfun1(X0,X1,sK1) | ~v1_partfun1(sK1,X0)) ) | ~spl2_1),
% 0.20/0.47    inference(resolution,[],[f27,f22])).
% 0.20/0.47  % (9586)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_partfun1(X0,X1,X2) = k1_tarski(X2) | ~v1_partfun1(X2,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_partfun1)).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    spl2_5 | ~spl2_1 | ~spl2_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f47,f38,f25,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    spl2_5 <=> sK1 = k3_partfun1(sK1,sK0,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    sK1 = k3_partfun1(sK1,sK0,sK0) | (~spl2_1 | ~spl2_3)),
% 0.20/0.47    inference(resolution,[],[f31,f40])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X4,X5] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | sK1 = k3_partfun1(sK1,X4,X5)) ) | ~spl2_1),
% 0.20/0.47    inference(resolution,[],[f27,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_partfun1(X2,X0,X1) = X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k3_partfun1(X2,X0,X1) = X2)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_partfun1)).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ~spl2_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f17,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    spl2_4 <=> k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) = k1_tarski(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    k5_partfun1(sK0,sK0,k3_partfun1(sK1,sK0,sK0)) != k1_tarski(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ? [X0,X1] : (k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.47    inference(flattening,[],[f6])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ? [X0,X1] : (k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) != k1_tarski(X1) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1))),
% 0.20/0.47    inference(negated_conjecture,[],[f4])).
% 0.20/0.47  fof(f4,conjecture,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k5_partfun1(X0,X0,k3_partfun1(X1,X0,X0)) = k1_tarski(X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_2)).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    spl2_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f16,f38])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    spl2_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f15,f33])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    spl2_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f14,f25])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    v1_funct_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (9584)------------------------------
% 0.20/0.47  % (9584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (9584)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (9584)Memory used [KB]: 10618
% 0.20/0.47  % (9584)Time elapsed: 0.058 s
% 0.20/0.47  % (9584)------------------------------
% 0.20/0.47  % (9584)------------------------------
% 0.20/0.47  % (9580)Success in time 0.115 s
%------------------------------------------------------------------------------

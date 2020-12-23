%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:38 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 131 expanded)
%              Number of leaves         :   18 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :  222 ( 502 expanded)
%              Number of equality atoms :   39 ( 104 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f53,f60,f74,f79,f84,f96,f108,f115,f123,f135])).

fof(f135,plain,
    ( spl4_12
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f131,f23])).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f131,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3))
    | spl4_12
    | ~ spl4_13 ),
    inference(superposition,[],[f95,f104])).

fof(f104,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_13
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f95,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK3))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_12
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f123,plain,
    ( ~ spl4_3
    | spl4_5
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl4_3
    | spl4_5
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f121,f42])).

fof(f42,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl4_3
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f121,plain,
    ( ~ r2_hidden(sK2,sK0)
    | spl4_5
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f117,f52])).

fof(f52,plain,
    ( sK2 != sK3
    | spl4_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_5
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f117,plain,
    ( sK2 = sK3
    | ~ r2_hidden(sK2,sK0)
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(superposition,[],[f107,f114])).

fof(f114,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_15
  <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f107,plain,
    ( ! [X0] :
        ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_14
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f115,plain,
    ( spl4_15
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f110,f106,f81,f45,f112])).

fof(f45,plain,
    ( spl4_4
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f81,plain,
    ( spl4_10
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f110,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f109,f47])).

fof(f47,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f109,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ r2_hidden(sK3,sK0)
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(superposition,[],[f107,f83])).

fof(f83,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f108,plain,
    ( spl4_13
    | spl4_14
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f98,f71,f57,f35,f30,f106,f102])).

fof(f30,plain,
    ( spl4_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f35,plain,
    ( spl4_2
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f57,plain,
    ( spl4_6
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f71,plain,
    ( spl4_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = sK0
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f97,f73])).

fof(f73,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f71])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = sK0
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(resolution,[],[f55,f59])).

fof(f59,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f55,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK1,X0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r2_hidden(X2,X0)
        | k1_xboole_0 = X1
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2 )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f54,f32])).

fof(f32,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f54,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK1,X0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(sK1)
        | ~ r2_hidden(X2,X0)
        | k1_xboole_0 = X1
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2 )
    | ~ spl4_2 ),
    inference(resolution,[],[f37,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f37,plain,
    ( v2_funct_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f96,plain,
    ( ~ spl4_12
    | spl4_9 ),
    inference(avatar_split_clause,[],[f86,f76,f93])).

fof(f76,plain,
    ( spl4_9
  <=> r1_tarski(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f86,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK3))
    | spl4_9 ),
    inference(resolution,[],[f78,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f78,plain,
    ( ~ r1_tarski(sK0,sK3)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f84,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f17,f81])).

fof(f17,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).

fof(f79,plain,
    ( ~ spl4_9
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f64,f45,f76])).

fof(f64,plain,
    ( ~ r1_tarski(sK0,sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f47,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f74,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f21,f71])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f60,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f20,f57])).

fof(f20,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f18,f50])).

fof(f18,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f16,f45])).

fof(f16,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f15,f40])).

fof(f15,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f38,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f22,f35])).

fof(f22,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f33,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f19,f30])).

fof(f19,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.44  % (28540)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.44  % (28540)Refutation found. Thanks to Tanya!
% 0.19/0.44  % SZS status Theorem for theBenchmark
% 0.19/0.45  % (28550)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f136,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f53,f60,f74,f79,f84,f96,f108,f115,f123,f135])).
% 0.19/0.45  fof(f135,plain,(
% 0.19/0.45    spl4_12 | ~spl4_13),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f134])).
% 0.19/0.45  fof(f134,plain,(
% 0.19/0.45    $false | (spl4_12 | ~spl4_13)),
% 0.19/0.45    inference(subsumption_resolution,[],[f131,f23])).
% 0.19/0.45  fof(f23,plain,(
% 0.19/0.45    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.19/0.45  fof(f131,plain,(
% 0.19/0.45    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) | (spl4_12 | ~spl4_13)),
% 0.19/0.45    inference(superposition,[],[f95,f104])).
% 0.19/0.45  fof(f104,plain,(
% 0.19/0.45    k1_xboole_0 = sK0 | ~spl4_13),
% 0.19/0.45    inference(avatar_component_clause,[],[f102])).
% 0.19/0.45  fof(f102,plain,(
% 0.19/0.45    spl4_13 <=> k1_xboole_0 = sK0),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.19/0.45  fof(f95,plain,(
% 0.19/0.45    ~m1_subset_1(sK0,k1_zfmisc_1(sK3)) | spl4_12),
% 0.19/0.45    inference(avatar_component_clause,[],[f93])).
% 0.19/0.45  fof(f93,plain,(
% 0.19/0.45    spl4_12 <=> m1_subset_1(sK0,k1_zfmisc_1(sK3))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.19/0.45  fof(f123,plain,(
% 0.19/0.45    ~spl4_3 | spl4_5 | ~spl4_14 | ~spl4_15),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f122])).
% 0.19/0.45  fof(f122,plain,(
% 0.19/0.45    $false | (~spl4_3 | spl4_5 | ~spl4_14 | ~spl4_15)),
% 0.19/0.45    inference(subsumption_resolution,[],[f121,f42])).
% 0.19/0.45  fof(f42,plain,(
% 0.19/0.45    r2_hidden(sK2,sK0) | ~spl4_3),
% 0.19/0.45    inference(avatar_component_clause,[],[f40])).
% 0.19/0.45  fof(f40,plain,(
% 0.19/0.45    spl4_3 <=> r2_hidden(sK2,sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.45  fof(f121,plain,(
% 0.19/0.45    ~r2_hidden(sK2,sK0) | (spl4_5 | ~spl4_14 | ~spl4_15)),
% 0.19/0.45    inference(subsumption_resolution,[],[f117,f52])).
% 0.19/0.45  fof(f52,plain,(
% 0.19/0.45    sK2 != sK3 | spl4_5),
% 0.19/0.45    inference(avatar_component_clause,[],[f50])).
% 0.19/0.45  fof(f50,plain,(
% 0.19/0.45    spl4_5 <=> sK2 = sK3),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.19/0.45  fof(f117,plain,(
% 0.19/0.45    sK2 = sK3 | ~r2_hidden(sK2,sK0) | (~spl4_14 | ~spl4_15)),
% 0.19/0.45    inference(superposition,[],[f107,f114])).
% 0.19/0.45  fof(f114,plain,(
% 0.19/0.45    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~spl4_15),
% 0.19/0.45    inference(avatar_component_clause,[],[f112])).
% 0.19/0.45  fof(f112,plain,(
% 0.19/0.45    spl4_15 <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.19/0.45  fof(f107,plain,(
% 0.19/0.45    ( ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,sK0)) ) | ~spl4_14),
% 0.19/0.45    inference(avatar_component_clause,[],[f106])).
% 0.19/0.45  fof(f106,plain,(
% 0.19/0.45    spl4_14 <=> ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.19/0.45  fof(f115,plain,(
% 0.19/0.45    spl4_15 | ~spl4_4 | ~spl4_10 | ~spl4_14),
% 0.19/0.45    inference(avatar_split_clause,[],[f110,f106,f81,f45,f112])).
% 0.19/0.45  fof(f45,plain,(
% 0.19/0.45    spl4_4 <=> r2_hidden(sK3,sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.19/0.45  fof(f81,plain,(
% 0.19/0.45    spl4_10 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.19/0.45  fof(f110,plain,(
% 0.19/0.45    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl4_4 | ~spl4_10 | ~spl4_14)),
% 0.19/0.45    inference(subsumption_resolution,[],[f109,f47])).
% 0.19/0.45  fof(f47,plain,(
% 0.19/0.45    r2_hidden(sK3,sK0) | ~spl4_4),
% 0.19/0.45    inference(avatar_component_clause,[],[f45])).
% 0.19/0.45  fof(f109,plain,(
% 0.19/0.45    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~r2_hidden(sK3,sK0) | (~spl4_10 | ~spl4_14)),
% 0.19/0.45    inference(superposition,[],[f107,f83])).
% 0.19/0.45  fof(f83,plain,(
% 0.19/0.45    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl4_10),
% 0.19/0.45    inference(avatar_component_clause,[],[f81])).
% 0.19/0.45  fof(f108,plain,(
% 0.19/0.45    spl4_13 | spl4_14 | ~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_8),
% 0.19/0.45    inference(avatar_split_clause,[],[f98,f71,f57,f35,f30,f106,f102])).
% 0.19/0.45  fof(f30,plain,(
% 0.19/0.45    spl4_1 <=> v1_funct_1(sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.45  fof(f35,plain,(
% 0.19/0.45    spl4_2 <=> v2_funct_1(sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.45  fof(f57,plain,(
% 0.19/0.45    spl4_6 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.19/0.45  fof(f71,plain,(
% 0.19/0.45    spl4_8 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.19/0.45  fof(f98,plain,(
% 0.19/0.45    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | (~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_8)),
% 0.19/0.45    inference(subsumption_resolution,[],[f97,f73])).
% 0.19/0.45  fof(f73,plain,(
% 0.19/0.45    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_8),
% 0.19/0.45    inference(avatar_component_clause,[],[f71])).
% 0.19/0.45  fof(f97,plain,(
% 0.19/0.45    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | (~spl4_1 | ~spl4_2 | ~spl4_6)),
% 0.19/0.45    inference(resolution,[],[f55,f59])).
% 0.19/0.45  fof(f59,plain,(
% 0.19/0.45    v1_funct_2(sK1,sK0,sK0) | ~spl4_6),
% 0.19/0.45    inference(avatar_component_clause,[],[f57])).
% 0.19/0.45  fof(f55,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~v1_funct_2(sK1,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2) ) | (~spl4_1 | ~spl4_2)),
% 0.19/0.45    inference(subsumption_resolution,[],[f54,f32])).
% 0.19/0.45  fof(f32,plain,(
% 0.19/0.45    v1_funct_1(sK1) | ~spl4_1),
% 0.19/0.45    inference(avatar_component_clause,[],[f30])).
% 0.19/0.45  fof(f54,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~v1_funct_2(sK1,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK1) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2) ) | ~spl4_2),
% 0.19/0.45    inference(resolution,[],[f37,f28])).
% 0.19/0.45  fof(f28,plain,(
% 0.19/0.45    ( ! [X2,X0,X3,X1] : (~v2_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) )),
% 0.19/0.45    inference(cnf_transformation,[],[f14])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.19/0.45    inference(flattening,[],[f13])).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.19/0.45    inference(ennf_transformation,[],[f5])).
% 0.19/0.45  fof(f5,axiom,(
% 0.19/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.19/0.45  fof(f37,plain,(
% 0.19/0.45    v2_funct_1(sK1) | ~spl4_2),
% 0.19/0.45    inference(avatar_component_clause,[],[f35])).
% 0.19/0.45  fof(f96,plain,(
% 0.19/0.45    ~spl4_12 | spl4_9),
% 0.19/0.45    inference(avatar_split_clause,[],[f86,f76,f93])).
% 0.19/0.45  fof(f76,plain,(
% 0.19/0.45    spl4_9 <=> r1_tarski(sK0,sK3)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.19/0.45  fof(f86,plain,(
% 0.19/0.45    ~m1_subset_1(sK0,k1_zfmisc_1(sK3)) | spl4_9),
% 0.19/0.45    inference(resolution,[],[f78,f25])).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.45  fof(f78,plain,(
% 0.19/0.45    ~r1_tarski(sK0,sK3) | spl4_9),
% 0.19/0.45    inference(avatar_component_clause,[],[f76])).
% 0.19/0.45  fof(f84,plain,(
% 0.19/0.45    spl4_10),
% 0.19/0.45    inference(avatar_split_clause,[],[f17,f81])).
% 0.19/0.45  fof(f17,plain,(
% 0.19/0.45    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.19/0.45    inference(cnf_transformation,[],[f9])).
% 0.19/0.45  fof(f9,plain,(
% 0.19/0.45    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.19/0.45    inference(flattening,[],[f8])).
% 0.19/0.45  fof(f8,plain,(
% 0.19/0.45    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.19/0.45    inference(ennf_transformation,[],[f7])).
% 0.19/0.45  fof(f7,negated_conjecture,(
% 0.19/0.45    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.19/0.45    inference(negated_conjecture,[],[f6])).
% 0.19/0.45  fof(f6,conjecture,(
% 0.19/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).
% 0.19/0.45  fof(f79,plain,(
% 0.19/0.45    ~spl4_9 | ~spl4_4),
% 0.19/0.45    inference(avatar_split_clause,[],[f64,f45,f76])).
% 0.19/0.45  fof(f64,plain,(
% 0.19/0.45    ~r1_tarski(sK0,sK3) | ~spl4_4),
% 0.19/0.45    inference(resolution,[],[f47,f26])).
% 0.19/0.45  fof(f26,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f10])).
% 0.19/0.45  fof(f10,plain,(
% 0.19/0.45    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.19/0.45    inference(ennf_transformation,[],[f4])).
% 0.19/0.45  fof(f4,axiom,(
% 0.19/0.45    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.19/0.45  fof(f74,plain,(
% 0.19/0.45    spl4_8),
% 0.19/0.45    inference(avatar_split_clause,[],[f21,f71])).
% 0.19/0.45  fof(f21,plain,(
% 0.19/0.45    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.45    inference(cnf_transformation,[],[f9])).
% 0.19/0.45  fof(f60,plain,(
% 0.19/0.45    spl4_6),
% 0.19/0.45    inference(avatar_split_clause,[],[f20,f57])).
% 0.19/0.45  fof(f20,plain,(
% 0.19/0.45    v1_funct_2(sK1,sK0,sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f9])).
% 0.19/0.45  fof(f53,plain,(
% 0.19/0.45    ~spl4_5),
% 0.19/0.45    inference(avatar_split_clause,[],[f18,f50])).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    sK2 != sK3),
% 0.19/0.45    inference(cnf_transformation,[],[f9])).
% 0.19/0.45  fof(f48,plain,(
% 0.19/0.45    spl4_4),
% 0.19/0.45    inference(avatar_split_clause,[],[f16,f45])).
% 0.19/0.45  fof(f16,plain,(
% 0.19/0.45    r2_hidden(sK3,sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f9])).
% 0.19/0.45  fof(f43,plain,(
% 0.19/0.45    spl4_3),
% 0.19/0.45    inference(avatar_split_clause,[],[f15,f40])).
% 0.19/0.45  fof(f15,plain,(
% 0.19/0.45    r2_hidden(sK2,sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f9])).
% 0.19/0.45  fof(f38,plain,(
% 0.19/0.45    spl4_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f22,f35])).
% 0.19/0.45  fof(f22,plain,(
% 0.19/0.45    v2_funct_1(sK1)),
% 0.19/0.45    inference(cnf_transformation,[],[f9])).
% 0.19/0.45  fof(f33,plain,(
% 0.19/0.45    spl4_1),
% 0.19/0.45    inference(avatar_split_clause,[],[f19,f30])).
% 0.19/0.45  fof(f19,plain,(
% 0.19/0.45    v1_funct_1(sK1)),
% 0.19/0.45    inference(cnf_transformation,[],[f9])).
% 0.19/0.45  % SZS output end Proof for theBenchmark
% 0.19/0.45  % (28540)------------------------------
% 0.19/0.45  % (28540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (28540)Termination reason: Refutation
% 0.19/0.45  
% 0.19/0.45  % (28540)Memory used [KB]: 10618
% 0.19/0.45  % (28540)Time elapsed: 0.045 s
% 0.19/0.45  % (28540)------------------------------
% 0.19/0.45  % (28540)------------------------------
% 0.19/0.45  % (28528)Success in time 0.099 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:44 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   51 (  69 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 179 expanded)
%              Number of equality atoms :   41 (  73 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f81,f89,f104])).

fof(f104,plain,
    ( spl3_1
    | spl3_2
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl3_1
    | spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f102,f32])).

fof(f32,plain,
    ( k1_xboole_0 != sK0
    | spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f102,plain,
    ( k1_xboole_0 = sK0
    | spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f101,f37])).

fof(f37,plain,
    ( k1_xboole_0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f101,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl3_9 ),
    inference(trivial_inequality_removal,[],[f99])).

fof(f99,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl3_9 ),
    inference(superposition,[],[f24,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_9
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f89,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f84,f78,f86])).

fof(f78,plain,
    ( spl3_8
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f84,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f80,f17])).

fof(f17,plain,(
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

fof(f80,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f81,plain,
    ( spl3_8
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f62,f45,f40,f78])).

fof(f40,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f45,plain,
    ( spl3_4
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f62,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3
    | spl3_4 ),
    inference(resolution,[],[f52,f42])).

fof(f42,plain,
    ( m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k2_zfmisc_1(X0,X1))
        | v1_xboole_0(k2_zfmisc_1(X0,X1)) )
    | spl3_4 ),
    inference(resolution,[],[f51,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f51,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK2,k2_zfmisc_1(X0,X1))
    | spl3_4 ),
    inference(resolution,[],[f50,f18])).

fof(f18,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f50,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(sK2,X0) )
    | spl3_4 ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,
    ( ! [X0] :
        ( sK2 != sK2
        | ~ r2_hidden(sK2,X0)
        | ~ v1_relat_1(X0) )
    | spl3_4 ),
    inference(superposition,[],[f47,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f47,plain,
    ( sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f48,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f14,f45])).

fof(f14,plain,(
    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f43,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f40])).

fof(f13,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f33,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f30])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:44:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.48  % (19764)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.48  % (19764)Refutation found. Thanks to Tanya!
% 0.23/0.48  % SZS status Theorem for theBenchmark
% 0.23/0.48  % SZS output start Proof for theBenchmark
% 0.23/0.48  fof(f105,plain,(
% 0.23/0.48    $false),
% 0.23/0.48    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f81,f89,f104])).
% 0.23/0.48  fof(f104,plain,(
% 0.23/0.48    spl3_1 | spl3_2 | ~spl3_9),
% 0.23/0.48    inference(avatar_contradiction_clause,[],[f103])).
% 0.23/0.48  fof(f103,plain,(
% 0.23/0.48    $false | (spl3_1 | spl3_2 | ~spl3_9)),
% 0.23/0.48    inference(subsumption_resolution,[],[f102,f32])).
% 0.23/0.48  fof(f32,plain,(
% 0.23/0.48    k1_xboole_0 != sK0 | spl3_1),
% 0.23/0.48    inference(avatar_component_clause,[],[f30])).
% 0.23/0.48  fof(f30,plain,(
% 0.23/0.48    spl3_1 <=> k1_xboole_0 = sK0),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.48  fof(f102,plain,(
% 0.23/0.48    k1_xboole_0 = sK0 | (spl3_2 | ~spl3_9)),
% 0.23/0.48    inference(subsumption_resolution,[],[f101,f37])).
% 0.23/0.48  fof(f37,plain,(
% 0.23/0.48    k1_xboole_0 != sK1 | spl3_2),
% 0.23/0.48    inference(avatar_component_clause,[],[f35])).
% 0.23/0.48  fof(f35,plain,(
% 0.23/0.48    spl3_2 <=> k1_xboole_0 = sK1),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.48  fof(f101,plain,(
% 0.23/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl3_9),
% 0.23/0.48    inference(trivial_inequality_removal,[],[f99])).
% 0.23/0.48  fof(f99,plain,(
% 0.23/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl3_9),
% 0.23/0.48    inference(superposition,[],[f24,f88])).
% 0.23/0.48  fof(f88,plain,(
% 0.23/0.48    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl3_9),
% 0.23/0.48    inference(avatar_component_clause,[],[f86])).
% 0.23/0.48  fof(f86,plain,(
% 0.23/0.48    spl3_9 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.23/0.48  fof(f24,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f2])).
% 0.23/0.48  fof(f2,axiom,(
% 0.23/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.23/0.48  fof(f89,plain,(
% 0.23/0.48    spl3_9 | ~spl3_8),
% 0.23/0.48    inference(avatar_split_clause,[],[f84,f78,f86])).
% 0.23/0.48  fof(f78,plain,(
% 0.23/0.48    spl3_8 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.23/0.48  fof(f84,plain,(
% 0.23/0.48    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl3_8),
% 0.23/0.48    inference(resolution,[],[f80,f17])).
% 0.23/0.48  fof(f17,plain,(
% 0.23/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f9])).
% 0.23/0.48  fof(f9,plain,(
% 0.23/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.23/0.48    inference(ennf_transformation,[],[f1])).
% 0.23/0.48  fof(f1,axiom,(
% 0.23/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.23/0.48  fof(f80,plain,(
% 0.23/0.48    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl3_8),
% 0.23/0.48    inference(avatar_component_clause,[],[f78])).
% 0.23/0.48  fof(f81,plain,(
% 0.23/0.48    spl3_8 | ~spl3_3 | spl3_4),
% 0.23/0.48    inference(avatar_split_clause,[],[f62,f45,f40,f78])).
% 0.23/0.48  fof(f40,plain,(
% 0.23/0.48    spl3_3 <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.23/0.48  fof(f45,plain,(
% 0.23/0.48    spl3_4 <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.23/0.48  fof(f62,plain,(
% 0.23/0.48    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | (~spl3_3 | spl3_4)),
% 0.23/0.48    inference(resolution,[],[f52,f42])).
% 0.23/0.48  fof(f42,plain,(
% 0.23/0.48    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_3),
% 0.23/0.48    inference(avatar_component_clause,[],[f40])).
% 0.23/0.48  fof(f52,plain,(
% 0.23/0.48    ( ! [X0,X1] : (~m1_subset_1(sK2,k2_zfmisc_1(X0,X1)) | v1_xboole_0(k2_zfmisc_1(X0,X1))) ) | spl3_4),
% 0.23/0.48    inference(resolution,[],[f51,f22])).
% 0.23/0.48  fof(f22,plain,(
% 0.23/0.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f10])).
% 0.23/0.48  fof(f10,plain,(
% 0.23/0.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.23/0.48    inference(ennf_transformation,[],[f3])).
% 0.23/0.48  fof(f3,axiom,(
% 0.23/0.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.23/0.48  fof(f51,plain,(
% 0.23/0.48    ( ! [X0,X1] : (~r2_hidden(sK2,k2_zfmisc_1(X0,X1))) ) | spl3_4),
% 0.23/0.48    inference(resolution,[],[f50,f18])).
% 0.23/0.48  fof(f18,plain,(
% 0.23/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f4])).
% 0.23/0.48  fof(f4,axiom,(
% 0.23/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.23/0.48  fof(f50,plain,(
% 0.23/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~r2_hidden(sK2,X0)) ) | spl3_4),
% 0.23/0.48    inference(trivial_inequality_removal,[],[f49])).
% 0.23/0.48  fof(f49,plain,(
% 0.23/0.48    ( ! [X0] : (sK2 != sK2 | ~r2_hidden(sK2,X0) | ~v1_relat_1(X0)) ) | spl3_4),
% 0.23/0.48    inference(superposition,[],[f47,f23])).
% 0.23/0.48  fof(f23,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f12])).
% 0.23/0.48  fof(f12,plain,(
% 0.23/0.48    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.23/0.48    inference(flattening,[],[f11])).
% 0.23/0.48  fof(f11,plain,(
% 0.23/0.48    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.23/0.48    inference(ennf_transformation,[],[f5])).
% 0.23/0.48  fof(f5,axiom,(
% 0.23/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.23/0.48  fof(f47,plain,(
% 0.23/0.48    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | spl3_4),
% 0.23/0.48    inference(avatar_component_clause,[],[f45])).
% 0.23/0.48  fof(f48,plain,(
% 0.23/0.48    ~spl3_4),
% 0.23/0.48    inference(avatar_split_clause,[],[f14,f45])).
% 0.23/0.48  fof(f14,plain,(
% 0.23/0.48    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.23/0.48    inference(cnf_transformation,[],[f8])).
% 0.23/0.48  fof(f8,plain,(
% 0.23/0.48    ? [X0,X1] : (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.23/0.48    inference(ennf_transformation,[],[f7])).
% 0.23/0.48  fof(f7,negated_conjecture,(
% 0.23/0.48    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.23/0.48    inference(negated_conjecture,[],[f6])).
% 0.23/0.48  fof(f6,conjecture,(
% 0.23/0.48    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).
% 0.23/0.48  fof(f43,plain,(
% 0.23/0.48    spl3_3),
% 0.23/0.48    inference(avatar_split_clause,[],[f13,f40])).
% 0.23/0.48  fof(f13,plain,(
% 0.23/0.48    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.23/0.48    inference(cnf_transformation,[],[f8])).
% 0.23/0.48  fof(f38,plain,(
% 0.23/0.48    ~spl3_2),
% 0.23/0.48    inference(avatar_split_clause,[],[f16,f35])).
% 0.23/0.48  fof(f16,plain,(
% 0.23/0.48    k1_xboole_0 != sK1),
% 0.23/0.48    inference(cnf_transformation,[],[f8])).
% 0.23/0.48  fof(f33,plain,(
% 0.23/0.48    ~spl3_1),
% 0.23/0.48    inference(avatar_split_clause,[],[f15,f30])).
% 0.23/0.48  fof(f15,plain,(
% 0.23/0.48    k1_xboole_0 != sK0),
% 0.23/0.48    inference(cnf_transformation,[],[f8])).
% 0.23/0.48  % SZS output end Proof for theBenchmark
% 0.23/0.48  % (19764)------------------------------
% 0.23/0.48  % (19764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.48  % (19764)Termination reason: Refutation
% 0.23/0.48  
% 0.23/0.48  % (19764)Memory used [KB]: 10618
% 0.23/0.48  % (19764)Time elapsed: 0.053 s
% 0.23/0.48  % (19764)------------------------------
% 0.23/0.48  % (19764)------------------------------
% 0.23/0.48  % (19760)Success in time 0.114 s
%------------------------------------------------------------------------------

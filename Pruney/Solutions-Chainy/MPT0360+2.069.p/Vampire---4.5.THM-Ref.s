%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 106 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :  185 ( 295 expanded)
%              Number of equality atoms :   30 (  52 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f31,f35,f39,f43,f47,f51,f56,f62,f70,f75,f80,f106,f118])).

fof(f118,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_9
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_9
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f116,f26])).

fof(f26,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f116,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_2
    | ~ spl3_9
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f112,f30])).

fof(f30,plain,
    ( k1_xboole_0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f112,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | ~ spl3_9
    | ~ spl3_18 ),
    inference(resolution,[],[f105,f61])).

fof(f61,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_9
  <=> r1_tarski(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f105,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(X4,k4_xboole_0(X5,X6))
        | k1_xboole_0 = X4
        | ~ r1_tarski(X4,X6) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl3_18
  <=> ! [X5,X4,X6] :
        ( ~ r1_tarski(X4,k4_xboole_0(X5,X6))
        | k1_xboole_0 = X4
        | ~ r1_tarski(X4,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f106,plain,
    ( spl3_18
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f83,f78,f73,f104])).

fof(f73,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))
        | ~ r1_tarski(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f78,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        | ~ r1_tarski(X2,X0)
        | k1_xboole_0 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f83,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(X4,k4_xboole_0(X5,X6))
        | k1_xboole_0 = X4
        | ~ r1_tarski(X4,X6) )
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(resolution,[],[f79,f74])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))
        | ~ r1_tarski(X2,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f73])).

fof(f79,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        | ~ r1_tarski(X2,X0)
        | k1_xboole_0 = X2 )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,
    ( spl3_13
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f52,f49,f45,f78])).

fof(f45,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f49,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f52,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        | ~ r1_tarski(X2,X0)
        | k1_xboole_0 = X2 )
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(resolution,[],[f50,f46])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
        | k1_xboole_0 = X0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f50,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f75,plain,
    ( spl3_12
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f71,f68,f41,f73])).

fof(f41,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f68,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X2,X1)
        | k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f71,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))
        | ~ r1_tarski(X2,X1) )
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(superposition,[],[f42,f69])).

fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        | ~ r1_tarski(X2,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f68])).

fof(f42,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f70,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f22,f68])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f62,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f58,f54,f37,f33,f60])).

fof(f33,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f37,plain,
    ( spl3_4
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f54,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f58,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f38,f57])).

fof(f57,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f55,f34])).

fof(f34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f38,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f56,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f20,f54])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f51,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f47,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f43,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f39,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f35,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f15,f33])).

fof(f15,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f18,f29])).

fof(f18,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f27,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f16,f25])).

fof(f16,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (30649)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.42  % (30649)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f119,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f27,f31,f35,f39,f43,f47,f51,f56,f62,f70,f75,f80,f106,f118])).
% 0.20/0.42  fof(f118,plain,(
% 0.20/0.42    ~spl3_1 | spl3_2 | ~spl3_9 | ~spl3_18),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f117])).
% 0.20/0.42  fof(f117,plain,(
% 0.20/0.42    $false | (~spl3_1 | spl3_2 | ~spl3_9 | ~spl3_18)),
% 0.20/0.42    inference(subsumption_resolution,[],[f116,f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    r1_tarski(sK1,sK2) | ~spl3_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    spl3_1 <=> r1_tarski(sK1,sK2)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.42  fof(f116,plain,(
% 0.20/0.42    ~r1_tarski(sK1,sK2) | (spl3_2 | ~spl3_9 | ~spl3_18)),
% 0.20/0.42    inference(subsumption_resolution,[],[f112,f30])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    k1_xboole_0 != sK1 | spl3_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f29])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    spl3_2 <=> k1_xboole_0 = sK1),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.42  fof(f112,plain,(
% 0.20/0.42    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | (~spl3_9 | ~spl3_18)),
% 0.20/0.42    inference(resolution,[],[f105,f61])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f60])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    spl3_9 <=> r1_tarski(sK1,k4_xboole_0(sK0,sK2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.42  fof(f105,plain,(
% 0.20/0.42    ( ! [X6,X4,X5] : (~r1_tarski(X4,k4_xboole_0(X5,X6)) | k1_xboole_0 = X4 | ~r1_tarski(X4,X6)) ) | ~spl3_18),
% 0.20/0.42    inference(avatar_component_clause,[],[f104])).
% 0.20/0.42  fof(f104,plain,(
% 0.20/0.42    spl3_18 <=> ! [X5,X4,X6] : (~r1_tarski(X4,k4_xboole_0(X5,X6)) | k1_xboole_0 = X4 | ~r1_tarski(X4,X6))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.42  fof(f106,plain,(
% 0.20/0.42    spl3_18 | ~spl3_12 | ~spl3_13),
% 0.20/0.42    inference(avatar_split_clause,[],[f83,f78,f73,f104])).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    spl3_12 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) | ~r1_tarski(X2,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    spl3_13 <=> ! [X1,X0,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X0) | k1_xboole_0 = X2)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    ( ! [X6,X4,X5] : (~r1_tarski(X4,k4_xboole_0(X5,X6)) | k1_xboole_0 = X4 | ~r1_tarski(X4,X6)) ) | (~spl3_12 | ~spl3_13)),
% 0.20/0.42    inference(resolution,[],[f79,f74])).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) | ~r1_tarski(X2,X1)) ) | ~spl3_12),
% 0.20/0.42    inference(avatar_component_clause,[],[f73])).
% 0.20/0.42  fof(f79,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X0) | k1_xboole_0 = X2) ) | ~spl3_13),
% 0.20/0.42    inference(avatar_component_clause,[],[f78])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    spl3_13 | ~spl3_6 | ~spl3_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f52,f49,f45,f78])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    spl3_6 <=> ! [X1,X0] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    spl3_7 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X0) | k1_xboole_0 = X2) ) | (~spl3_6 | ~spl3_7)),
% 0.20/0.42    inference(resolution,[],[f50,f46])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) ) | ~spl3_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f45])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f49])).
% 0.20/0.42  fof(f75,plain,(
% 0.20/0.42    spl3_12 | ~spl3_5 | ~spl3_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f71,f68,f41,f73])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    spl3_5 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    spl3_11 <=> ! [X1,X0,X2] : (~r1_tarski(X2,X1) | k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) | ~r1_tarski(X2,X1)) ) | (~spl3_5 | ~spl3_11)),
% 0.20/0.42    inference(superposition,[],[f42,f69])).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) | ~r1_tarski(X2,X1)) ) | ~spl3_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f68])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f41])).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    spl3_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f68])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) | ~r1_tarski(X2,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    spl3_9 | ~spl3_3 | ~spl3_4 | ~spl3_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f58,f54,f37,f33,f60])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    spl3_4 <=> r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    spl3_8 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_8)),
% 0.20/0.42    inference(backward_demodulation,[],[f38,f57])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | (~spl3_3 | ~spl3_8)),
% 0.20/0.42    inference(resolution,[],[f55,f34])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f33])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) ) | ~spl3_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f54])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~spl3_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f37])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    spl3_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f20,f54])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    spl3_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f23,f49])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(flattening,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    spl3_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f21,f45])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    spl3_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f19,f41])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    spl3_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f17,f37])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.42    inference(flattening,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.20/0.42    inference(negated_conjecture,[],[f6])).
% 0.20/0.42  fof(f6,conjecture,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    spl3_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f15,f33])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ~spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f18,f29])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    k1_xboole_0 != sK1),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    spl3_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f16,f25])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    r1_tarski(sK1,sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (30649)------------------------------
% 0.20/0.42  % (30649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (30649)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (30649)Memory used [KB]: 10618
% 0.20/0.42  % (30649)Time elapsed: 0.007 s
% 0.20/0.42  % (30649)------------------------------
% 0.20/0.42  % (30649)------------------------------
% 0.20/0.42  % (30639)Success in time 0.069 s
%------------------------------------------------------------------------------

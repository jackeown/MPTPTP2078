%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 (  93 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :  160 ( 246 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f57,f65,f73,f92,f100,f104,f146,f157])).

fof(f157,plain,
    ( spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f78,f155])).

fof(f155,plain,
    ( r1_tarski(k1_tarski(k4_tarski(sK0,sK2)),k2_zfmisc_1(sK1,sK3))
    | ~ spl4_4
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f150,f120])).

fof(f120,plain,
    ( ! [X4,X3] : k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4))
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f118,f56])).

fof(f56,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f55])).

% (4711)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f55,plain,
    ( spl4_4
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f118,plain,
    ( ! [X4,X3] : k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k2_tarski(X4,X4))
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(superposition,[],[f103,f56])).

fof(f103,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_14
  <=> ! [X1,X0,X2] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f150,plain,
    ( r1_tarski(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK2)),k2_zfmisc_1(sK1,sK3))
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_19 ),
    inference(unit_resulting_resolution,[],[f91,f145,f99])).

fof(f99,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_13
  <=> ! [X1,X3,X0,X2] :
        ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f145,plain,
    ( r1_tarski(k1_tarski(sK2),sK3)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_19
  <=> r1_tarski(k1_tarski(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f91,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_11
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f78,plain,
    ( ~ r1_tarski(k1_tarski(k4_tarski(sK0,sK2)),k2_zfmisc_1(sK1,sK3))
    | spl4_3
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f52,f64])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f52,plain,
    ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_3
  <=> m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f146,plain,
    ( spl4_19
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f82,f71,f45,f143])).

fof(f45,plain,
    ( spl4_2
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f71,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f82,plain,
    ( r1_tarski(k1_tarski(sK2),sK3)
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f47,f72])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f71])).

fof(f47,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f104,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f32,f102])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f100,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f35,f98])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f92,plain,
    ( spl4_11
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f81,f71,f40,f89])).

fof(f40,plain,
    ( spl4_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f81,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f42,f72])).

fof(f42,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f73,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f30,f71])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f65,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f57,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f25,f55])).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    & r2_hidden(sK2,sK3)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & r2_hidden(X2,X3)
        & r2_hidden(X0,X1) )
   => ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      & r2_hidden(sK2,sK3)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r2_hidden(X2,X3)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r2_hidden(X2,X3)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X2,X3)
          & r2_hidden(X0,X1) )
       => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X2,X3)
        & r2_hidden(X0,X1) )
     => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_relset_1)).

fof(f48,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f22,f40])).

fof(f22,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:58:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (4712)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (4718)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (4718)Refutation not found, incomplete strategy% (4718)------------------------------
% 0.21/0.48  % (4718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4712)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f43,f48,f53,f57,f65,f73,f92,f100,f104,f146,f157])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_11 | ~spl4_13 | ~spl4_14 | ~spl4_19),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f156])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    $false | (spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_11 | ~spl4_13 | ~spl4_14 | ~spl4_19)),
% 0.21/0.48    inference(subsumption_resolution,[],[f78,f155])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    r1_tarski(k1_tarski(k4_tarski(sK0,sK2)),k2_zfmisc_1(sK1,sK3)) | (~spl4_4 | ~spl4_11 | ~spl4_13 | ~spl4_14 | ~spl4_19)),
% 0.21/0.48    inference(forward_demodulation,[],[f150,f120])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ( ! [X4,X3] : (k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4))) ) | (~spl4_4 | ~spl4_14)),
% 0.21/0.48    inference(forward_demodulation,[],[f118,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f55])).
% 0.21/0.48  % (4711)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl4_4 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ( ! [X4,X3] : (k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k2_tarski(X4,X4))) ) | (~spl4_4 | ~spl4_14)),
% 0.21/0.48    inference(superposition,[],[f103,f56])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) ) | ~spl4_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    spl4_14 <=> ! [X1,X0,X2] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    r1_tarski(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK2)),k2_zfmisc_1(sK1,sK3)) | (~spl4_11 | ~spl4_13 | ~spl4_19)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f91,f145,f99])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) ) | ~spl4_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    spl4_13 <=> ! [X1,X3,X0,X2] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    r1_tarski(k1_tarski(sK2),sK3) | ~spl4_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f143])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    spl4_19 <=> r1_tarski(k1_tarski(sK2),sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    r1_tarski(k1_tarski(sK0),sK1) | ~spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl4_11 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ~r1_tarski(k1_tarski(k4_tarski(sK0,sK2)),k2_zfmisc_1(sK1,sK3)) | (spl4_3 | ~spl4_6)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f52,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl4_6 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl4_3 <=> m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    spl4_19 | ~spl4_2 | ~spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f82,f71,f45,f143])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    spl4_2 <=> r2_hidden(sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl4_8 <=> ! [X1,X0] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    r1_tarski(k1_tarski(sK2),sK3) | (~spl4_2 | ~spl4_8)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f47,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl4_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f71])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    r2_hidden(sK2,sK3) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f45])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl4_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f102])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl4_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f98])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl4_11 | ~spl4_1 | ~spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f81,f71,f40,f89])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl4_1 <=> r2_hidden(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    r1_tarski(k1_tarski(sK0),sK1) | (~spl4_1 | ~spl4_8)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f42,f72])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    r2_hidden(sK0,sK1) | ~spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f40])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f71])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl4_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f63])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f55])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ~spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f50])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) & r2_hidden(sK2,sK3) & r2_hidden(sK0,sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r2_hidden(X2,X3) & r2_hidden(X0,X1)) => (~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) & r2_hidden(sK2,sK3) & r2_hidden(sK0,sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r2_hidden(X2,X3) & r2_hidden(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & (r2_hidden(X2,X3) & r2_hidden(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : ((r2_hidden(X2,X3) & r2_hidden(X0,X1)) => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),
% 0.21/0.48    inference(negated_conjecture,[],[f12])).
% 0.21/0.48  fof(f12,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((r2_hidden(X2,X3) & r2_hidden(X0,X1)) => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_relset_1)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f45])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    r2_hidden(sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f22,f40])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    r2_hidden(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (4712)------------------------------
% 0.21/0.48  % (4712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4712)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (4712)Memory used [KB]: 6140
% 0.21/0.48  % (4712)Time elapsed: 0.054 s
% 0.21/0.48  % (4712)------------------------------
% 0.21/0.48  % (4712)------------------------------
% 0.21/0.48  % (4710)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (4718)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (4718)Memory used [KB]: 10618
% 0.21/0.48  % (4718)Time elapsed: 0.065 s
% 0.21/0.48  % (4718)------------------------------
% 0.21/0.48  % (4718)------------------------------
% 0.21/0.48  % (4706)Success in time 0.115 s
%------------------------------------------------------------------------------

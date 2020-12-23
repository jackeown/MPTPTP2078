%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 121 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :    6
%              Number of atoms          :  214 ( 336 expanded)
%              Number of equality atoms :   56 (  97 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f270,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f49,f53,f57,f61,f65,f69,f144,f150,f156,f172,f215,f231,f257,f269])).

fof(f269,plain,
    ( spl3_25
    | ~ spl3_6
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f268,f255,f55,f148])).

fof(f148,plain,
    ( spl3_25
  <=> ! [X1,X0] :
        ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f55,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f255,plain,
    ( spl3_39
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK0,k2_zfmisc_1(X0,X1))
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f268,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1)) )
    | ~ spl3_6
    | ~ spl3_39 ),
    inference(resolution,[],[f256,f56])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f256,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK0,k2_zfmisc_1(X0,X1))
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f255])).

fof(f257,plain,
    ( spl3_39
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f234,f67,f33,f255])).

fof(f33,plain,
    ( spl3_1
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f67,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( k1_mcart_1(X2) != X2
        | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f234,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK0,k2_zfmisc_1(X0,X1))
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 )
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(trivial_inequality_removal,[],[f233])).

fof(f233,plain,
    ( ! [X0,X1] :
        ( sK0 != sK0
        | ~ m1_subset_1(sK0,k2_zfmisc_1(X0,X1))
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 )
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(superposition,[],[f68,f35])).

fof(f35,plain,
    ( sK0 = k1_mcart_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( k1_mcart_1(X2) != X2
        | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f231,plain,
    ( spl3_28
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f230,f169,f59,f47,f175])).

fof(f175,plain,
    ( spl3_28
  <=> ! [X0] : r2_hidden(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f47,plain,
    ( spl3_4
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f59,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f169,plain,
    ( spl3_27
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f230,plain,
    ( ! [X3] : r2_hidden(sK0,X3)
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f220,f48])).

fof(f48,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f220,plain,
    ( ! [X3] :
        ( r2_hidden(sK0,X3)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3)) )
    | ~ spl3_7
    | ~ spl3_27 ),
    inference(resolution,[],[f171,f60])).

fof(f60,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X1)
        | r2_hidden(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f171,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f169])).

fof(f215,plain,
    ( ~ spl3_5
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_28 ),
    inference(resolution,[],[f176,f52])).

fof(f52,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_5
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f176,plain,
    ( ! [X0] : r2_hidden(sK0,X0)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f175])).

fof(f172,plain,
    ( spl3_27
    | ~ spl3_3
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f157,f153,f42,f169])).

fof(f42,plain,
    ( spl3_3
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f153,plain,
    ( spl3_26
  <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f157,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_26 ),
    inference(superposition,[],[f44,f155])).

fof(f155,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f153])).

fof(f44,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f156,plain,
    ( spl3_26
    | ~ spl3_3
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f151,f148,f42,f153])).

fof(f151,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | ~ spl3_3
    | ~ spl3_25 ),
    inference(resolution,[],[f149,f44])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1))
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f148])).

fof(f150,plain,
    ( spl3_25
    | ~ spl3_2
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f146,f142,f37,f148])).

fof(f37,plain,
    ( spl3_2
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f142,plain,
    ( spl3_24
  <=> ! [X1,X0,X2] :
        ( k2_mcart_1(X0) != X0
        | k1_xboole_0 = k2_zfmisc_1(X1,X2)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1)) )
    | ~ spl3_2
    | ~ spl3_24 ),
    inference(trivial_inequality_removal,[],[f145])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( sK0 != sK0
        | k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1)) )
    | ~ spl3_2
    | ~ spl3_24 ),
    inference(superposition,[],[f143,f39])).

fof(f39,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f143,plain,
    ( ! [X2,X0,X1] :
        ( k2_mcart_1(X0) != X0
        | k1_xboole_0 = k2_zfmisc_1(X1,X2)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f142])).

fof(f144,plain,
    ( spl3_24
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f140,f63,f55,f142])).

fof(f63,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( k2_mcart_1(X2) != X2
        | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f140,plain,
    ( ! [X2,X0,X1] :
        ( k2_mcart_1(X0) != X0
        | k1_xboole_0 = k2_zfmisc_1(X1,X2)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(resolution,[],[f64,f56])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
        | k2_mcart_1(X2) != X2
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f69,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f26,f67])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 )
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
     => ! [X2] :
          ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
         => ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_mcart_1)).

fof(f65,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f57,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f24,f55])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f53,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f23,f51])).

fof(f23,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f49,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_mcart_1)).

fof(f40,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f21,f37,f33])).

fof(f21,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:05:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.44  % (15422)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.44  % (15420)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (15421)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (15419)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.45  % (15420)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f270,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f40,f45,f49,f53,f57,f61,f65,f69,f144,f150,f156,f172,f215,f231,f257,f269])).
% 0.22/0.45  fof(f269,plain,(
% 0.22/0.45    spl3_25 | ~spl3_6 | ~spl3_39),
% 0.22/0.45    inference(avatar_split_clause,[],[f268,f255,f55,f148])).
% 0.22/0.45  fof(f148,plain,(
% 0.22/0.45    spl3_25 <=> ! [X1,X0] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | ~r2_hidden(sK0,k2_zfmisc_1(X0,X1)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    spl3_6 <=> ! [X1,X0] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.45  fof(f255,plain,(
% 0.22/0.45    spl3_39 <=> ! [X1,X0] : (~m1_subset_1(sK0,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.22/0.45  fof(f268,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | ~r2_hidden(sK0,k2_zfmisc_1(X0,X1))) ) | (~spl3_6 | ~spl3_39)),
% 0.22/0.45    inference(resolution,[],[f256,f56])).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) ) | ~spl3_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f55])).
% 0.22/0.45  fof(f256,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~m1_subset_1(sK0,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) ) | ~spl3_39),
% 0.22/0.45    inference(avatar_component_clause,[],[f255])).
% 0.22/0.45  fof(f257,plain,(
% 0.22/0.45    spl3_39 | ~spl3_1 | ~spl3_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f234,f67,f33,f255])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    spl3_1 <=> sK0 = k1_mcart_1(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    spl3_9 <=> ! [X1,X0,X2] : (k1_mcart_1(X2) != X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.45  fof(f234,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~m1_subset_1(sK0,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) ) | (~spl3_1 | ~spl3_9)),
% 0.22/0.45    inference(trivial_inequality_removal,[],[f233])).
% 0.22/0.45  fof(f233,plain,(
% 0.22/0.45    ( ! [X0,X1] : (sK0 != sK0 | ~m1_subset_1(sK0,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) ) | (~spl3_1 | ~spl3_9)),
% 0.22/0.45    inference(superposition,[],[f68,f35])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    sK0 = k1_mcart_1(sK0) | ~spl3_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f33])).
% 0.22/0.45  fof(f68,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k1_mcart_1(X2) != X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) ) | ~spl3_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f67])).
% 0.22/0.45  fof(f231,plain,(
% 0.22/0.45    spl3_28 | ~spl3_4 | ~spl3_7 | ~spl3_27),
% 0.22/0.45    inference(avatar_split_clause,[],[f230,f169,f59,f47,f175])).
% 0.22/0.45  fof(f175,plain,(
% 0.22/0.45    spl3_28 <=> ! [X0] : r2_hidden(sK0,X0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    spl3_4 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    spl3_7 <=> ! [X1,X0,X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.45  fof(f169,plain,(
% 0.22/0.45    spl3_27 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.45  fof(f230,plain,(
% 0.22/0.45    ( ! [X3] : (r2_hidden(sK0,X3)) ) | (~spl3_4 | ~spl3_7 | ~spl3_27)),
% 0.22/0.45    inference(subsumption_resolution,[],[f220,f48])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl3_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f47])).
% 0.22/0.45  fof(f220,plain,(
% 0.22/0.45    ( ! [X3] : (r2_hidden(sK0,X3) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))) ) | (~spl3_7 | ~spl3_27)),
% 0.22/0.45    inference(resolution,[],[f171,f60])).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f59])).
% 0.22/0.45  fof(f171,plain,(
% 0.22/0.45    r2_hidden(sK0,k1_xboole_0) | ~spl3_27),
% 0.22/0.45    inference(avatar_component_clause,[],[f169])).
% 0.22/0.45  fof(f215,plain,(
% 0.22/0.45    ~spl3_5 | ~spl3_28),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f210])).
% 0.22/0.45  fof(f210,plain,(
% 0.22/0.45    $false | (~spl3_5 | ~spl3_28)),
% 0.22/0.45    inference(resolution,[],[f176,f52])).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl3_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f51])).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    spl3_5 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.45  fof(f176,plain,(
% 0.22/0.45    ( ! [X0] : (r2_hidden(sK0,X0)) ) | ~spl3_28),
% 0.22/0.45    inference(avatar_component_clause,[],[f175])).
% 0.22/0.45  fof(f172,plain,(
% 0.22/0.45    spl3_27 | ~spl3_3 | ~spl3_26),
% 0.22/0.45    inference(avatar_split_clause,[],[f157,f153,f42,f169])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    spl3_3 <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.45  fof(f153,plain,(
% 0.22/0.45    spl3_26 <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.45  fof(f157,plain,(
% 0.22/0.45    r2_hidden(sK0,k1_xboole_0) | (~spl3_3 | ~spl3_26)),
% 0.22/0.45    inference(superposition,[],[f44,f155])).
% 0.22/0.45  fof(f155,plain,(
% 0.22/0.45    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) | ~spl3_26),
% 0.22/0.45    inference(avatar_component_clause,[],[f153])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | ~spl3_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f42])).
% 0.22/0.45  fof(f156,plain,(
% 0.22/0.45    spl3_26 | ~spl3_3 | ~spl3_25),
% 0.22/0.45    inference(avatar_split_clause,[],[f151,f148,f42,f153])).
% 0.22/0.45  fof(f151,plain,(
% 0.22/0.45    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) | (~spl3_3 | ~spl3_25)),
% 0.22/0.45    inference(resolution,[],[f149,f44])).
% 0.22/0.45  fof(f149,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) ) | ~spl3_25),
% 0.22/0.45    inference(avatar_component_clause,[],[f148])).
% 0.22/0.45  fof(f150,plain,(
% 0.22/0.45    spl3_25 | ~spl3_2 | ~spl3_24),
% 0.22/0.45    inference(avatar_split_clause,[],[f146,f142,f37,f148])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    spl3_2 <=> sK0 = k2_mcart_1(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.45  fof(f142,plain,(
% 0.22/0.45    spl3_24 <=> ! [X1,X0,X2] : (k2_mcart_1(X0) != X0 | k1_xboole_0 = k2_zfmisc_1(X1,X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.45  fof(f146,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | ~r2_hidden(sK0,k2_zfmisc_1(X0,X1))) ) | (~spl3_2 | ~spl3_24)),
% 0.22/0.45    inference(trivial_inequality_removal,[],[f145])).
% 0.22/0.45  fof(f145,plain,(
% 0.22/0.45    ( ! [X0,X1] : (sK0 != sK0 | k2_zfmisc_1(X0,X1) = k1_xboole_0 | ~r2_hidden(sK0,k2_zfmisc_1(X0,X1))) ) | (~spl3_2 | ~spl3_24)),
% 0.22/0.45    inference(superposition,[],[f143,f39])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    sK0 = k2_mcart_1(sK0) | ~spl3_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f37])).
% 0.22/0.45  fof(f143,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k1_xboole_0 = k2_zfmisc_1(X1,X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) ) | ~spl3_24),
% 0.22/0.45    inference(avatar_component_clause,[],[f142])).
% 0.22/0.45  fof(f144,plain,(
% 0.22/0.45    spl3_24 | ~spl3_6 | ~spl3_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f140,f63,f55,f142])).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    spl3_8 <=> ! [X1,X0,X2] : (k2_mcart_1(X2) != X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.45  fof(f140,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k1_xboole_0 = k2_zfmisc_1(X1,X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) ) | (~spl3_6 | ~spl3_8)),
% 0.22/0.45    inference(resolution,[],[f64,f56])).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k2_mcart_1(X2) != X2 | k2_zfmisc_1(X0,X1) = k1_xboole_0) ) | ~spl3_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f63])).
% 0.22/0.45  fof(f69,plain,(
% 0.22/0.45    spl3_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f26,f67])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k1_mcart_1(X2) != X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0,X1] : (! [X2] : ((k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2) | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k2_zfmisc_1(X0,X1) = k1_xboole_0)),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 => ! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_mcart_1)).
% 0.22/0.45  fof(f65,plain,(
% 0.22/0.45    spl3_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f27,f63])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k2_mcart_1(X2) != X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    spl3_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f25,f59])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    spl3_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f24,f55])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    spl3_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f23,f51])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    spl3_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f22,f47])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    spl3_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f20,f42])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ? [X0,X1,X2] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ? [X0,X1,X2] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.22/0.45    inference(negated_conjecture,[],[f8])).
% 0.22/0.45  fof(f8,conjecture,(
% 0.22/0.45    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_mcart_1)).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    spl3_1 | spl3_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f21,f37,f33])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (15420)------------------------------
% 0.22/0.45  % (15420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (15420)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (15420)Memory used [KB]: 10618
% 0.22/0.45  % (15420)Time elapsed: 0.014 s
% 0.22/0.45  % (15420)------------------------------
% 0.22/0.45  % (15420)------------------------------
% 0.22/0.46  % (15414)Success in time 0.098 s
%------------------------------------------------------------------------------

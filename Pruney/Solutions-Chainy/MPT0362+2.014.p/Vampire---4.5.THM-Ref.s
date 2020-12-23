%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:05 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 132 expanded)
%              Number of leaves         :   19 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :  200 ( 313 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f214,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f58,f87,f117,f126,f140,f147,f158,f183,f192,f213])).

fof(f213,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | ~ spl5_4 ),
    inference(resolution,[],[f200,f21])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f200,plain,
    ( ! [X0] : ~ r1_tarski(X0,sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f196,f35])).

fof(f35,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f196,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f61,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f61,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_4
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f192,plain,
    ( ~ spl5_7
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | ~ spl5_7
    | spl5_14 ),
    inference(subsumption_resolution,[],[f190,f86])).

fof(f86,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_7
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f190,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK0))
    | spl5_14 ),
    inference(resolution,[],[f182,f34])).

fof(f34,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f182,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl5_14
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f183,plain,
    ( ~ spl5_14
    | spl5_13 ),
    inference(avatar_split_clause,[],[f172,f155,f180])).

fof(f155,plain,
    ( spl5_13
  <=> r1_tarski(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f172,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl5_13 ),
    inference(resolution,[],[f163,f21])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
        | ~ r1_tarski(X0,sK0) )
    | spl5_13 ),
    inference(resolution,[],[f157,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f157,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f155])).

fof(f158,plain,
    ( ~ spl5_13
    | spl5_12 ),
    inference(avatar_split_clause,[],[f149,f144,f155])).

fof(f144,plain,
    ( spl5_12
  <=> r2_hidden(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f149,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK0)
    | spl5_12 ),
    inference(resolution,[],[f146,f35])).

fof(f146,plain,
    ( ~ r2_hidden(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f144])).

fof(f147,plain,
    ( ~ spl5_12
    | spl5_4
    | spl5_11 ),
    inference(avatar_split_clause,[],[f141,f137,f60,f144])).

fof(f137,plain,
    ( spl5_11
  <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f141,plain,
    ( ~ r2_hidden(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | spl5_4
    | spl5_11 ),
    inference(resolution,[],[f139,f102])).

fof(f102,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ r2_hidden(X0,k1_zfmisc_1(sK0)) )
    | spl5_4 ),
    inference(resolution,[],[f62,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f62,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f139,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f140,plain,
    ( ~ spl5_11
    | ~ spl5_2
    | spl5_10 ),
    inference(avatar_split_clause,[],[f135,f123,f42,f137])).

fof(f42,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f123,plain,
    ( spl5_10
  <=> r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f135,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl5_2
    | spl5_10 ),
    inference(subsumption_resolution,[],[f134,f21])).

fof(f134,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ spl5_2
    | spl5_10 ),
    inference(subsumption_resolution,[],[f131,f44])).

fof(f44,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f131,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | spl5_10 ),
    inference(resolution,[],[f125,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f125,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2)))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f126,plain,
    ( ~ spl5_10
    | spl5_9 ),
    inference(avatar_split_clause,[],[f120,f114,f123])).

fof(f114,plain,
    ( spl5_9
  <=> r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(k3_subset_1(sK0,k3_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f120,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2)))
    | spl5_9 ),
    inference(resolution,[],[f116,f35])).

fof(f116,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(k3_subset_1(sK0,k3_xboole_0(sK1,sK2))))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f117,plain,
    ( ~ spl5_9
    | ~ spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f108,f55,f37,f114])).

fof(f37,plain,
    ( spl5_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f55,plain,
    ( spl5_3
  <=> r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f108,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(k3_subset_1(sK0,k3_xboole_0(sK1,sK2))))
    | ~ spl5_1
    | spl5_3 ),
    inference(forward_demodulation,[],[f70,f46])).

fof(f46,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f39,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f70,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))))
    | spl5_3 ),
    inference(resolution,[],[f57,f34])).

fof(f57,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f87,plain,
    ( spl5_7
    | ~ spl5_2
    | spl5_4 ),
    inference(avatar_split_clause,[],[f82,f60,f42,f84])).

fof(f82,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f53,f62])).

fof(f53,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f44,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f17,f55])).

fof(f17,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

fof(f45,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f16,f37])).

fof(f16,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 12:12:45 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.44  % (17205)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.23/0.49  % (17189)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.23/0.50  % (17192)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.50  % (17202)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.23/0.50  % (17201)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.23/0.51  % (17187)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.23/0.51  % (17187)Refutation not found, incomplete strategy% (17187)------------------------------
% 0.23/0.51  % (17187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (17187)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (17187)Memory used [KB]: 6140
% 0.23/0.51  % (17187)Time elapsed: 0.085 s
% 0.23/0.51  % (17187)------------------------------
% 0.23/0.51  % (17187)------------------------------
% 0.23/0.51  % (17195)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.23/0.51  % (17193)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.51  % (17200)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.51  % (17188)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.51  % (17196)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.23/0.51  % (17190)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.51  % (17198)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.23/0.51  % (17190)Refutation found. Thanks to Tanya!
% 0.23/0.51  % SZS status Theorem for theBenchmark
% 0.23/0.51  % SZS output start Proof for theBenchmark
% 0.23/0.51  fof(f214,plain,(
% 0.23/0.51    $false),
% 0.23/0.51    inference(avatar_sat_refutation,[],[f40,f45,f58,f87,f117,f126,f140,f147,f158,f183,f192,f213])).
% 0.23/0.51  fof(f213,plain,(
% 0.23/0.51    ~spl5_4),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f209])).
% 0.23/0.51  fof(f209,plain,(
% 0.23/0.51    $false | ~spl5_4),
% 0.23/0.51    inference(resolution,[],[f200,f21])).
% 0.23/0.51  fof(f21,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f2])).
% 0.23/0.51  fof(f2,axiom,(
% 0.23/0.51    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.23/0.51  fof(f200,plain,(
% 0.23/0.51    ( ! [X0] : (~r1_tarski(X0,sK0)) ) | ~spl5_4),
% 0.23/0.51    inference(resolution,[],[f196,f35])).
% 0.23/0.51  fof(f35,plain,(
% 0.23/0.51    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 0.23/0.51    inference(equality_resolution,[],[f28])).
% 0.23/0.51  fof(f28,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.23/0.51    inference(cnf_transformation,[],[f4])).
% 0.23/0.51  fof(f4,axiom,(
% 0.23/0.51    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.23/0.51  fof(f196,plain,(
% 0.23/0.51    ( ! [X1] : (~r2_hidden(X1,k1_zfmisc_1(sK0))) ) | ~spl5_4),
% 0.23/0.51    inference(resolution,[],[f61,f20])).
% 0.23/0.51  fof(f20,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f1])).
% 0.23/0.51  fof(f1,axiom,(
% 0.23/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.23/0.51  fof(f61,plain,(
% 0.23/0.51    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_4),
% 0.23/0.51    inference(avatar_component_clause,[],[f60])).
% 0.23/0.51  fof(f60,plain,(
% 0.23/0.51    spl5_4 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.23/0.51  fof(f192,plain,(
% 0.23/0.51    ~spl5_7 | spl5_14),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f191])).
% 0.23/0.51  fof(f191,plain,(
% 0.23/0.51    $false | (~spl5_7 | spl5_14)),
% 0.23/0.51    inference(subsumption_resolution,[],[f190,f86])).
% 0.23/0.51  fof(f86,plain,(
% 0.23/0.51    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_7),
% 0.23/0.51    inference(avatar_component_clause,[],[f84])).
% 0.23/0.51  fof(f84,plain,(
% 0.23/0.51    spl5_7 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.23/0.51  fof(f190,plain,(
% 0.23/0.51    ~r2_hidden(sK1,k1_zfmisc_1(sK0)) | spl5_14),
% 0.23/0.51    inference(resolution,[],[f182,f34])).
% 0.23/0.51  fof(f34,plain,(
% 0.23/0.51    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.23/0.51    inference(equality_resolution,[],[f29])).
% 0.23/0.51  fof(f29,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.23/0.51    inference(cnf_transformation,[],[f4])).
% 0.23/0.51  fof(f182,plain,(
% 0.23/0.51    ~r1_tarski(sK1,sK0) | spl5_14),
% 0.23/0.51    inference(avatar_component_clause,[],[f180])).
% 0.23/0.51  fof(f180,plain,(
% 0.23/0.51    spl5_14 <=> r1_tarski(sK1,sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.23/0.51  fof(f183,plain,(
% 0.23/0.51    ~spl5_14 | spl5_13),
% 0.23/0.51    inference(avatar_split_clause,[],[f172,f155,f180])).
% 0.23/0.51  fof(f155,plain,(
% 0.23/0.51    spl5_13 <=> r1_tarski(k3_xboole_0(sK1,sK2),sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.23/0.51  fof(f172,plain,(
% 0.23/0.51    ~r1_tarski(sK1,sK0) | spl5_13),
% 0.23/0.51    inference(resolution,[],[f163,f21])).
% 0.23/0.51  fof(f163,plain,(
% 0.23/0.51    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~r1_tarski(X0,sK0)) ) | spl5_13),
% 0.23/0.51    inference(resolution,[],[f157,f33])).
% 0.23/0.51  fof(f33,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f15])).
% 0.23/0.52  fof(f15,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.23/0.52    inference(flattening,[],[f14])).
% 0.23/0.52  fof(f14,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.23/0.52    inference(ennf_transformation,[],[f3])).
% 0.23/0.52  fof(f3,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.23/0.52  fof(f157,plain,(
% 0.23/0.52    ~r1_tarski(k3_xboole_0(sK1,sK2),sK0) | spl5_13),
% 0.23/0.52    inference(avatar_component_clause,[],[f155])).
% 0.23/0.52  fof(f158,plain,(
% 0.23/0.52    ~spl5_13 | spl5_12),
% 0.23/0.52    inference(avatar_split_clause,[],[f149,f144,f155])).
% 0.23/0.52  fof(f144,plain,(
% 0.23/0.52    spl5_12 <=> r2_hidden(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.23/0.52  fof(f149,plain,(
% 0.23/0.52    ~r1_tarski(k3_xboole_0(sK1,sK2),sK0) | spl5_12),
% 0.23/0.52    inference(resolution,[],[f146,f35])).
% 0.23/0.52  fof(f146,plain,(
% 0.23/0.52    ~r2_hidden(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | spl5_12),
% 0.23/0.52    inference(avatar_component_clause,[],[f144])).
% 0.23/0.52  fof(f147,plain,(
% 0.23/0.52    ~spl5_12 | spl5_4 | spl5_11),
% 0.23/0.52    inference(avatar_split_clause,[],[f141,f137,f60,f144])).
% 0.23/0.52  fof(f137,plain,(
% 0.23/0.52    spl5_11 <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.23/0.52  fof(f141,plain,(
% 0.23/0.52    ~r2_hidden(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | (spl5_4 | spl5_11)),
% 0.23/0.52    inference(resolution,[],[f139,f102])).
% 0.23/0.52  fof(f102,plain,(
% 0.23/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(X0,k1_zfmisc_1(sK0))) ) | spl5_4),
% 0.23/0.52    inference(resolution,[],[f62,f24])).
% 0.23/0.52  fof(f24,plain,(
% 0.23/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f11])).
% 0.23/0.52  fof(f11,plain,(
% 0.23/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.23/0.52    inference(ennf_transformation,[],[f5])).
% 0.23/0.52  fof(f5,axiom,(
% 0.23/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.23/0.52  fof(f62,plain,(
% 0.23/0.52    ~v1_xboole_0(k1_zfmisc_1(sK0)) | spl5_4),
% 0.23/0.52    inference(avatar_component_clause,[],[f60])).
% 0.23/0.52  fof(f139,plain,(
% 0.23/0.52    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | spl5_11),
% 0.23/0.52    inference(avatar_component_clause,[],[f137])).
% 0.23/0.52  fof(f140,plain,(
% 0.23/0.52    ~spl5_11 | ~spl5_2 | spl5_10),
% 0.23/0.52    inference(avatar_split_clause,[],[f135,f123,f42,f137])).
% 0.23/0.52  fof(f42,plain,(
% 0.23/0.52    spl5_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.23/0.52  fof(f123,plain,(
% 0.23/0.52    spl5_10 <=> r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2)))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.23/0.52  fof(f135,plain,(
% 0.23/0.52    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | (~spl5_2 | spl5_10)),
% 0.23/0.52    inference(subsumption_resolution,[],[f134,f21])).
% 0.23/0.52  fof(f134,plain,(
% 0.23/0.52    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | (~spl5_2 | spl5_10)),
% 0.23/0.52    inference(subsumption_resolution,[],[f131,f44])).
% 0.23/0.52  fof(f44,plain,(
% 0.23/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_2),
% 0.23/0.52    inference(avatar_component_clause,[],[f42])).
% 0.23/0.52  fof(f131,plain,(
% 0.23/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | spl5_10),
% 0.23/0.52    inference(resolution,[],[f125,f27])).
% 0.23/0.52  fof(f27,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X2)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f12])).
% 0.23/0.52  fof(f12,plain,(
% 0.23/0.52    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.52    inference(ennf_transformation,[],[f7])).
% 0.23/0.52  fof(f7,axiom,(
% 0.23/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 0.23/0.52  fof(f125,plain,(
% 0.23/0.52    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2))) | spl5_10),
% 0.23/0.52    inference(avatar_component_clause,[],[f123])).
% 0.23/0.52  fof(f126,plain,(
% 0.23/0.52    ~spl5_10 | spl5_9),
% 0.23/0.52    inference(avatar_split_clause,[],[f120,f114,f123])).
% 0.23/0.52  fof(f114,plain,(
% 0.23/0.52    spl5_9 <=> r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(k3_subset_1(sK0,k3_xboole_0(sK1,sK2))))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.23/0.52  fof(f120,plain,(
% 0.23/0.52    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2))) | spl5_9),
% 0.23/0.52    inference(resolution,[],[f116,f35])).
% 0.23/0.52  fof(f116,plain,(
% 0.23/0.52    ~r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(k3_subset_1(sK0,k3_xboole_0(sK1,sK2)))) | spl5_9),
% 0.23/0.52    inference(avatar_component_clause,[],[f114])).
% 0.23/0.52  fof(f117,plain,(
% 0.23/0.52    ~spl5_9 | ~spl5_1 | spl5_3),
% 0.23/0.52    inference(avatar_split_clause,[],[f108,f55,f37,f114])).
% 0.23/0.52  fof(f37,plain,(
% 0.23/0.52    spl5_1 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.23/0.52  fof(f55,plain,(
% 0.23/0.52    spl5_3 <=> r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.23/0.52  fof(f108,plain,(
% 0.23/0.52    ~r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(k3_subset_1(sK0,k3_xboole_0(sK1,sK2)))) | (~spl5_1 | spl5_3)),
% 0.23/0.52    inference(forward_demodulation,[],[f70,f46])).
% 0.23/0.52  fof(f46,plain,(
% 0.23/0.52    ( ! [X0] : (k9_subset_1(sK0,X0,sK2) = k3_xboole_0(X0,sK2)) ) | ~spl5_1),
% 0.23/0.52    inference(resolution,[],[f39,f32])).
% 0.23/0.52  fof(f32,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f13])).
% 0.23/0.52  fof(f13,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.23/0.52    inference(ennf_transformation,[],[f6])).
% 0.23/0.52  fof(f6,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.23/0.52  fof(f39,plain,(
% 0.23/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl5_1),
% 0.23/0.52    inference(avatar_component_clause,[],[f37])).
% 0.23/0.52  fof(f70,plain,(
% 0.23/0.52    ~r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))) | spl5_3),
% 0.23/0.52    inference(resolution,[],[f57,f34])).
% 0.23/0.52  fof(f57,plain,(
% 0.23/0.52    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) | spl5_3),
% 0.23/0.52    inference(avatar_component_clause,[],[f55])).
% 0.23/0.52  fof(f87,plain,(
% 0.23/0.52    spl5_7 | ~spl5_2 | spl5_4),
% 0.23/0.52    inference(avatar_split_clause,[],[f82,f60,f42,f84])).
% 0.23/0.52  fof(f82,plain,(
% 0.23/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0)) | (~spl5_2 | spl5_4)),
% 0.23/0.52    inference(subsumption_resolution,[],[f53,f62])).
% 0.23/0.52  fof(f53,plain,(
% 0.23/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_2),
% 0.23/0.52    inference(resolution,[],[f44,f25])).
% 0.23/0.52  fof(f25,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f11])).
% 0.23/0.52  fof(f58,plain,(
% 0.23/0.52    ~spl5_3),
% 0.23/0.52    inference(avatar_split_clause,[],[f17,f55])).
% 0.23/0.52  fof(f17,plain,(
% 0.23/0.52    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 0.23/0.52    inference(cnf_transformation,[],[f10])).
% 0.23/0.52  fof(f10,plain,(
% 0.23/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.52    inference(ennf_transformation,[],[f9])).
% 0.23/0.52  fof(f9,negated_conjecture,(
% 0.23/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 0.23/0.52    inference(negated_conjecture,[],[f8])).
% 0.23/0.52  fof(f8,conjecture,(
% 0.23/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).
% 0.23/0.52  fof(f45,plain,(
% 0.23/0.52    spl5_2),
% 0.23/0.52    inference(avatar_split_clause,[],[f18,f42])).
% 0.23/0.52  fof(f18,plain,(
% 0.23/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.52    inference(cnf_transformation,[],[f10])).
% 0.23/0.52  fof(f40,plain,(
% 0.23/0.52    spl5_1),
% 0.23/0.52    inference(avatar_split_clause,[],[f16,f37])).
% 0.23/0.52  fof(f16,plain,(
% 0.23/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.23/0.52    inference(cnf_transformation,[],[f10])).
% 0.23/0.52  % SZS output end Proof for theBenchmark
% 0.23/0.52  % (17190)------------------------------
% 0.23/0.52  % (17190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (17190)Termination reason: Refutation
% 0.23/0.52  
% 0.23/0.52  % (17190)Memory used [KB]: 10618
% 0.23/0.52  % (17190)Time elapsed: 0.085 s
% 0.23/0.52  % (17190)------------------------------
% 0.23/0.52  % (17190)------------------------------
% 0.23/0.52  % (17186)Success in time 0.147 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 104 expanded)
%              Number of leaves         :   12 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :  155 ( 318 expanded)
%              Number of equality atoms :   12 (  33 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (27980)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f383,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f40,f149,f195,f205,f225,f355,f377,f378])).

fof(f378,plain,
    ( ~ spl5_12
    | spl5_13
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f373,f352,f110,f106])).

fof(f106,plain,
    ( spl5_12
  <=> r2_hidden(sK4(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f110,plain,
    ( spl5_13
  <=> r2_hidden(sK4(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f352,plain,
    ( spl5_35
  <=> m1_subset_1(sK4(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f373,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | ~ r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl5_35 ),
    inference(resolution,[],[f354,f13])).

fof(f13,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f354,plain,
    ( m1_subset_1(sK4(sK1,sK2),sK0)
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f352])).

fof(f377,plain,
    ( spl5_12
    | ~ spl5_13
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f374,f352,f110,f106])).

fof(f374,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK2)
    | r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl5_35 ),
    inference(resolution,[],[f354,f12])).

fof(f12,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f355,plain,
    ( spl5_35
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f349,f192,f352])).

fof(f192,plain,
    ( spl5_21
  <=> r2_hidden(sK4(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f349,plain,
    ( m1_subset_1(sK4(sK1,sK2),sK0)
    | ~ spl5_21 ),
    inference(resolution,[],[f194,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f18,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f194,plain,
    ( r2_hidden(sK4(sK1,sK2),sK0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f192])).

fof(f225,plain,
    ( spl5_21
    | ~ spl5_3
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f214,f110,f37,f192])).

fof(f37,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f214,plain,
    ( r2_hidden(sK4(sK1,sK2),sK0)
    | ~ spl5_3
    | ~ spl5_13 ),
    inference(resolution,[],[f96,f112])).

fof(f112,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f110])).

fof(f96,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,sK0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f23,f39])).

fof(f39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f205,plain,
    ( spl5_2
    | spl5_13
    | spl5_12 ),
    inference(avatar_split_clause,[],[f204,f106,f110,f32])).

fof(f32,plain,
    ( spl5_2
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f204,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | sK1 = sK2
    | spl5_12 ),
    inference(resolution,[],[f107,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f107,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK1)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f195,plain,
    ( spl5_21
    | ~ spl5_1
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f185,f106,f27,f192])).

fof(f27,plain,
    ( spl5_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f185,plain,
    ( r2_hidden(sK4(sK1,sK2),sK0)
    | ~ spl5_1
    | ~ spl5_12 ),
    inference(resolution,[],[f95,f108])).

fof(f108,plain,
    ( r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f23,f29])).

fof(f29,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f149,plain,
    ( ~ spl5_12
    | ~ spl5_13
    | spl5_2 ),
    inference(avatar_split_clause,[],[f133,f32,f110,f106])).

fof(f133,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK2)
    | ~ r2_hidden(sK4(sK1,sK2),sK1)
    | spl5_2 ),
    inference(extensionality_resolution,[],[f25,f34])).

fof(f34,plain,
    ( sK1 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f14,f37])).

fof(f14,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f15,f32])).

fof(f15,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f16,f27])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:25:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (27962)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (27971)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (27960)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (27979)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (27967)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (27970)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (27984)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (27975)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (27968)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (27961)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (27975)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (27963)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (27985)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (27961)Refutation not found, incomplete strategy% (27961)------------------------------
% 0.21/0.54  % (27961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27961)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27961)Memory used [KB]: 10746
% 0.21/0.54  % (27961)Time elapsed: 0.123 s
% 0.21/0.54  % (27961)------------------------------
% 0.21/0.54  % (27961)------------------------------
% 0.21/0.54  % (27970)Refutation not found, incomplete strategy% (27970)------------------------------
% 0.21/0.54  % (27970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27979)Refutation not found, incomplete strategy% (27979)------------------------------
% 0.21/0.54  % (27979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27979)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27979)Memory used [KB]: 10746
% 0.21/0.54  % (27979)Time elapsed: 0.128 s
% 0.21/0.54  % (27979)------------------------------
% 0.21/0.54  % (27979)------------------------------
% 0.21/0.54  % (27976)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (27968)Refutation not found, incomplete strategy% (27968)------------------------------
% 0.21/0.54  % (27968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27970)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27970)Memory used [KB]: 10746
% 0.21/0.54  % (27970)Time elapsed: 0.118 s
% 0.21/0.54  % (27970)------------------------------
% 0.21/0.54  % (27970)------------------------------
% 0.21/0.54  % (27985)Refutation not found, incomplete strategy% (27985)------------------------------
% 0.21/0.54  % (27985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27982)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (27968)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27968)Memory used [KB]: 10746
% 0.21/0.54  % (27968)Time elapsed: 0.123 s
% 0.21/0.54  % (27968)------------------------------
% 0.21/0.54  % (27968)------------------------------
% 0.21/0.55  % (27976)Refutation not found, incomplete strategy% (27976)------------------------------
% 0.21/0.55  % (27976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27985)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27986)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (27985)Memory used [KB]: 10618
% 0.21/0.55  % (27985)Time elapsed: 0.129 s
% 0.21/0.55  % (27985)------------------------------
% 0.21/0.55  % (27985)------------------------------
% 0.21/0.55  % (27988)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (27978)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (27976)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27976)Memory used [KB]: 10618
% 0.21/0.55  % (27976)Time elapsed: 0.128 s
% 0.21/0.55  % (27976)------------------------------
% 0.21/0.55  % (27976)------------------------------
% 0.21/0.55  % (27959)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (27977)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (27972)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  % (27980)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  fof(f383,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f30,f35,f40,f149,f195,f205,f225,f355,f377,f378])).
% 0.21/0.56  fof(f378,plain,(
% 0.21/0.56    ~spl5_12 | spl5_13 | ~spl5_35),
% 0.21/0.56    inference(avatar_split_clause,[],[f373,f352,f110,f106])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    spl5_12 <=> r2_hidden(sK4(sK1,sK2),sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.56  fof(f110,plain,(
% 0.21/0.56    spl5_13 <=> r2_hidden(sK4(sK1,sK2),sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.56  fof(f352,plain,(
% 0.21/0.56    spl5_35 <=> m1_subset_1(sK4(sK1,sK2),sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.21/0.56  fof(f373,plain,(
% 0.21/0.56    r2_hidden(sK4(sK1,sK2),sK2) | ~r2_hidden(sK4(sK1,sK2),sK1) | ~spl5_35),
% 0.21/0.56    inference(resolution,[],[f354,f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ( ! [X3] : (~m1_subset_1(X3,sK0) | r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,plain,(
% 0.21/0.56    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(flattening,[],[f7])).
% 0.21/0.56  fof(f7,plain,(
% 0.21/0.56    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.56    inference(negated_conjecture,[],[f5])).
% 0.21/0.56  fof(f5,conjecture,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 0.21/0.56  fof(f354,plain,(
% 0.21/0.56    m1_subset_1(sK4(sK1,sK2),sK0) | ~spl5_35),
% 0.21/0.56    inference(avatar_component_clause,[],[f352])).
% 0.21/0.56  fof(f377,plain,(
% 0.21/0.56    spl5_12 | ~spl5_13 | ~spl5_35),
% 0.21/0.56    inference(avatar_split_clause,[],[f374,f352,f110,f106])).
% 0.21/0.56  fof(f374,plain,(
% 0.21/0.56    ~r2_hidden(sK4(sK1,sK2),sK2) | r2_hidden(sK4(sK1,sK2),sK1) | ~spl5_35),
% 0.21/0.56    inference(resolution,[],[f354,f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f355,plain,(
% 0.21/0.56    spl5_35 | ~spl5_21),
% 0.21/0.56    inference(avatar_split_clause,[],[f349,f192,f352])).
% 0.21/0.56  fof(f192,plain,(
% 0.21/0.56    spl5_21 <=> r2_hidden(sK4(sK1,sK2),sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.56  fof(f349,plain,(
% 0.21/0.56    m1_subset_1(sK4(sK1,sK2),sK0) | ~spl5_21),
% 0.21/0.56    inference(resolution,[],[f194,f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.56    inference(global_subsumption,[],[f18,f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,plain,(
% 0.21/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.56  fof(f194,plain,(
% 0.21/0.56    r2_hidden(sK4(sK1,sK2),sK0) | ~spl5_21),
% 0.21/0.56    inference(avatar_component_clause,[],[f192])).
% 0.21/0.56  fof(f225,plain,(
% 0.21/0.56    spl5_21 | ~spl5_3 | ~spl5_13),
% 0.21/0.56    inference(avatar_split_clause,[],[f214,f110,f37,f192])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    spl5_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.56  fof(f214,plain,(
% 0.21/0.56    r2_hidden(sK4(sK1,sK2),sK0) | (~spl5_3 | ~spl5_13)),
% 0.21/0.56    inference(resolution,[],[f96,f112])).
% 0.21/0.56  fof(f112,plain,(
% 0.21/0.56    r2_hidden(sK4(sK1,sK2),sK2) | ~spl5_13),
% 0.21/0.56    inference(avatar_component_clause,[],[f110])).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(X1,sK2) | r2_hidden(X1,sK0)) ) | ~spl5_3),
% 0.21/0.56    inference(resolution,[],[f23,f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl5_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f37])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,plain,(
% 0.21/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.56  fof(f205,plain,(
% 0.21/0.56    spl5_2 | spl5_13 | spl5_12),
% 0.21/0.56    inference(avatar_split_clause,[],[f204,f106,f110,f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    spl5_2 <=> sK1 = sK2),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.56  fof(f204,plain,(
% 0.21/0.56    r2_hidden(sK4(sK1,sK2),sK2) | sK1 = sK2 | spl5_12),
% 0.21/0.56    inference(resolution,[],[f107,f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    ~r2_hidden(sK4(sK1,sK2),sK1) | spl5_12),
% 0.21/0.56    inference(avatar_component_clause,[],[f106])).
% 0.21/0.56  fof(f195,plain,(
% 0.21/0.56    spl5_21 | ~spl5_1 | ~spl5_12),
% 0.21/0.56    inference(avatar_split_clause,[],[f185,f106,f27,f192])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    spl5_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.56  fof(f185,plain,(
% 0.21/0.56    r2_hidden(sK4(sK1,sK2),sK0) | (~spl5_1 | ~spl5_12)),
% 0.21/0.56    inference(resolution,[],[f95,f108])).
% 0.21/0.56  fof(f108,plain,(
% 0.21/0.56    r2_hidden(sK4(sK1,sK2),sK1) | ~spl5_12),
% 0.21/0.56    inference(avatar_component_clause,[],[f106])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) ) | ~spl5_1),
% 0.21/0.56    inference(resolution,[],[f23,f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f27])).
% 0.21/0.56  fof(f149,plain,(
% 0.21/0.56    ~spl5_12 | ~spl5_13 | spl5_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f133,f32,f110,f106])).
% 0.21/0.56  fof(f133,plain,(
% 0.21/0.56    ~r2_hidden(sK4(sK1,sK2),sK2) | ~r2_hidden(sK4(sK1,sK2),sK1) | spl5_2),
% 0.21/0.56    inference(extensionality_resolution,[],[f25,f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    sK1 != sK2 | spl5_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f32])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    spl5_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f14,f37])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ~spl5_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f15,f32])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    sK1 != sK2),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    spl5_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f16,f27])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (27975)------------------------------
% 0.21/0.56  % (27975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (27975)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (27975)Memory used [KB]: 10874
% 0.21/0.56  % (27975)Time elapsed: 0.128 s
% 0.21/0.56  % (27975)------------------------------
% 0.21/0.56  % (27975)------------------------------
% 0.21/0.56  % (27969)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (27983)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (27958)Success in time 0.193 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:10 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   63 (  96 expanded)
%              Number of leaves         :   15 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :  158 ( 249 expanded)
%              Number of equality atoms :   14 (  29 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f213,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f44,f52,f62,f74,f93,f125,f163,f212])).

fof(f212,plain,
    ( ~ spl8_6
    | ~ spl8_7
    | spl8_9 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_7
    | spl8_9 ),
    inference(subsumption_resolution,[],[f209,f120])).

fof(f120,plain,
    ( ~ r2_hidden(sK7(sK0),sK2)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl8_9
  <=> r2_hidden(sK7(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f209,plain,
    ( r2_hidden(sK7(sK0),sK2)
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(resolution,[],[f102,f73])).

fof(f73,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl8_6
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f102,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3))
        | r2_hidden(sK7(sK0),X3) )
    | ~ spl8_7 ),
    inference(superposition,[],[f29,f92])).

fof(f92,plain,
    ( sK0 = k4_tarski(sK6(sK0),sK7(sK0))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl8_7
  <=> sK0 = k4_tarski(sK6(sK0),sK7(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f163,plain,
    ( spl8_10
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f156,f90,f71,f122])).

fof(f122,plain,
    ( spl8_10
  <=> r2_hidden(sK6(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f156,plain,
    ( r2_hidden(sK6(sK0),sK1)
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(resolution,[],[f101,f73])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1))
        | r2_hidden(sK6(sK0),X0) )
    | ~ spl8_7 ),
    inference(superposition,[],[f28,f92])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f125,plain,
    ( ~ spl8_9
    | ~ spl8_10
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f103,f90,f122,f118])).

fof(f103,plain,
    ( ~ r2_hidden(sK6(sK0),sK1)
    | ~ r2_hidden(sK7(sK0),sK2)
    | ~ spl8_7 ),
    inference(trivial_inequality_removal,[],[f100])).

fof(f100,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK6(sK0),sK1)
    | ~ r2_hidden(sK7(sK0),sK2)
    | ~ spl8_7 ),
    inference(superposition,[],[f15,f92])).

fof(f15,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK0
      | ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ~ ( ! [X4,X5] :
                ~ ( r2_hidden(X5,X2)
                  & r2_hidden(X4,X1)
                  & k4_tarski(X4,X5) = X0 )
            & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

fof(f93,plain,
    ( spl8_7
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f81,f71,f90])).

fof(f81,plain,
    ( sK0 = k4_tarski(sK6(sK0),sK7(sK0))
    | ~ spl8_6 ),
    inference(resolution,[],[f73,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK6(X0),sK7(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f74,plain,
    ( spl8_6
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f63,f59,f34,f71])).

fof(f34,plain,
    ( spl8_1
  <=> r2_hidden(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f59,plain,
    ( spl8_4
  <=> r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f63,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f61,f39])).

fof(f39,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK3,X2)
        | r2_hidden(sK0,X2) )
    | ~ spl8_1 ),
    inference(resolution,[],[f36,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f36,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f61,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f62,plain,
    ( spl8_4
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f53,f49,f59])).

fof(f49,plain,
    ( spl8_3
  <=> r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f53,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
    | ~ spl8_3 ),
    inference(resolution,[],[f51,f31])).

fof(f31,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f51,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f52,plain,
    ( spl8_3
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f46,f41,f49])).

fof(f41,plain,
    ( spl8_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f46,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f45,f18])).

fof(f18,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f45,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl8_2 ),
    inference(resolution,[],[f43,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f44,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f16,f41])).

fof(f16,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f10])).

fof(f37,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    r2_hidden(sK0,sK3) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.53  % (19975)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (19991)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (19983)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (19972)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (19965)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (19965)Refutation not found, incomplete strategy% (19965)------------------------------
% 0.21/0.56  % (19965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (19965)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (19965)Memory used [KB]: 10618
% 0.21/0.56  % (19965)Time elapsed: 0.149 s
% 0.21/0.56  % (19965)------------------------------
% 0.21/0.56  % (19965)------------------------------
% 0.21/0.56  % (19988)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (19980)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.56/0.58  % (19983)Refutation found. Thanks to Tanya!
% 1.56/0.58  % SZS status Theorem for theBenchmark
% 1.56/0.59  % SZS output start Proof for theBenchmark
% 1.56/0.59  fof(f213,plain,(
% 1.56/0.59    $false),
% 1.56/0.59    inference(avatar_sat_refutation,[],[f37,f44,f52,f62,f74,f93,f125,f163,f212])).
% 1.56/0.59  fof(f212,plain,(
% 1.56/0.59    ~spl8_6 | ~spl8_7 | spl8_9),
% 1.56/0.59    inference(avatar_contradiction_clause,[],[f211])).
% 1.56/0.59  fof(f211,plain,(
% 1.56/0.59    $false | (~spl8_6 | ~spl8_7 | spl8_9)),
% 1.56/0.59    inference(subsumption_resolution,[],[f209,f120])).
% 1.56/0.59  fof(f120,plain,(
% 1.56/0.59    ~r2_hidden(sK7(sK0),sK2) | spl8_9),
% 1.56/0.59    inference(avatar_component_clause,[],[f118])).
% 1.56/0.59  fof(f118,plain,(
% 1.56/0.59    spl8_9 <=> r2_hidden(sK7(sK0),sK2)),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.56/0.59  fof(f209,plain,(
% 1.56/0.59    r2_hidden(sK7(sK0),sK2) | (~spl8_6 | ~spl8_7)),
% 1.56/0.59    inference(resolution,[],[f102,f73])).
% 1.56/0.59  fof(f73,plain,(
% 1.56/0.59    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | ~spl8_6),
% 1.56/0.59    inference(avatar_component_clause,[],[f71])).
% 1.56/0.59  fof(f71,plain,(
% 1.56/0.59    spl8_6 <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.56/0.59  fof(f102,plain,(
% 1.56/0.59    ( ! [X2,X3] : (~r2_hidden(sK0,k2_zfmisc_1(X2,X3)) | r2_hidden(sK7(sK0),X3)) ) | ~spl8_7),
% 1.56/0.59    inference(superposition,[],[f29,f92])).
% 1.56/0.59  fof(f92,plain,(
% 1.56/0.59    sK0 = k4_tarski(sK6(sK0),sK7(sK0)) | ~spl8_7),
% 1.56/0.59    inference(avatar_component_clause,[],[f90])).
% 1.56/0.59  fof(f90,plain,(
% 1.56/0.59    spl8_7 <=> sK0 = k4_tarski(sK6(sK0),sK7(sK0))),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.56/0.59  fof(f29,plain,(
% 1.56/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f4])).
% 1.56/0.59  fof(f4,axiom,(
% 1.56/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.56/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.56/0.59  fof(f163,plain,(
% 1.56/0.59    spl8_10 | ~spl8_6 | ~spl8_7),
% 1.56/0.59    inference(avatar_split_clause,[],[f156,f90,f71,f122])).
% 1.56/0.59  fof(f122,plain,(
% 1.56/0.59    spl8_10 <=> r2_hidden(sK6(sK0),sK1)),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.56/0.59  fof(f156,plain,(
% 1.56/0.59    r2_hidden(sK6(sK0),sK1) | (~spl8_6 | ~spl8_7)),
% 1.56/0.59    inference(resolution,[],[f101,f73])).
% 1.56/0.59  fof(f101,plain,(
% 1.56/0.59    ( ! [X0,X1] : (~r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | r2_hidden(sK6(sK0),X0)) ) | ~spl8_7),
% 1.56/0.59    inference(superposition,[],[f28,f92])).
% 1.56/0.59  fof(f28,plain,(
% 1.56/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f4])).
% 1.56/0.59  fof(f125,plain,(
% 1.56/0.59    ~spl8_9 | ~spl8_10 | ~spl8_7),
% 1.56/0.59    inference(avatar_split_clause,[],[f103,f90,f122,f118])).
% 1.56/0.59  fof(f103,plain,(
% 1.56/0.59    ~r2_hidden(sK6(sK0),sK1) | ~r2_hidden(sK7(sK0),sK2) | ~spl8_7),
% 1.56/0.59    inference(trivial_inequality_removal,[],[f100])).
% 1.56/0.59  fof(f100,plain,(
% 1.56/0.59    sK0 != sK0 | ~r2_hidden(sK6(sK0),sK1) | ~r2_hidden(sK7(sK0),sK2) | ~spl8_7),
% 1.56/0.59    inference(superposition,[],[f15,f92])).
% 1.56/0.59  fof(f15,plain,(
% 1.56/0.59    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK0 | ~r2_hidden(X4,sK1) | ~r2_hidden(X5,sK2)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f10])).
% 1.56/0.59  fof(f10,plain,(
% 1.56/0.59    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.56/0.59    inference(flattening,[],[f9])).
% 1.56/0.59  fof(f9,plain,(
% 1.56/0.59    ? [X0,X1,X2,X3] : ((! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.56/0.59    inference(ennf_transformation,[],[f8])).
% 1.56/0.59  fof(f8,negated_conjecture,(
% 1.56/0.59    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 1.56/0.59    inference(negated_conjecture,[],[f7])).
% 1.56/0.59  fof(f7,conjecture,(
% 1.56/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 1.56/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).
% 1.56/0.59  fof(f93,plain,(
% 1.56/0.59    spl8_7 | ~spl8_6),
% 1.56/0.59    inference(avatar_split_clause,[],[f81,f71,f90])).
% 1.56/0.59  fof(f81,plain,(
% 1.56/0.59    sK0 = k4_tarski(sK6(sK0),sK7(sK0)) | ~spl8_6),
% 1.56/0.59    inference(resolution,[],[f73,f27])).
% 1.56/0.59  fof(f27,plain,(
% 1.56/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK6(X0),sK7(X0)) = X0) )),
% 1.56/0.59    inference(cnf_transformation,[],[f14])).
% 1.56/0.59  fof(f14,plain,(
% 1.56/0.59    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.56/0.59    inference(ennf_transformation,[],[f3])).
% 1.56/0.59  fof(f3,axiom,(
% 1.56/0.59    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.56/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 1.56/0.59  fof(f74,plain,(
% 1.56/0.59    spl8_6 | ~spl8_1 | ~spl8_4),
% 1.56/0.59    inference(avatar_split_clause,[],[f63,f59,f34,f71])).
% 1.56/0.59  fof(f34,plain,(
% 1.56/0.59    spl8_1 <=> r2_hidden(sK0,sK3)),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.56/0.59  fof(f59,plain,(
% 1.56/0.59    spl8_4 <=> r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.56/0.59  fof(f63,plain,(
% 1.56/0.59    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | (~spl8_1 | ~spl8_4)),
% 1.56/0.59    inference(resolution,[],[f61,f39])).
% 1.56/0.59  fof(f39,plain,(
% 1.56/0.59    ( ! [X2] : (~r1_tarski(sK3,X2) | r2_hidden(sK0,X2)) ) | ~spl8_1),
% 1.56/0.59    inference(resolution,[],[f36,f20])).
% 1.56/0.59  fof(f20,plain,(
% 1.56/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f13])).
% 1.56/0.59  fof(f13,plain,(
% 1.56/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.56/0.59    inference(ennf_transformation,[],[f1])).
% 1.56/0.59  fof(f1,axiom,(
% 1.56/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.56/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.56/0.59  fof(f36,plain,(
% 1.56/0.59    r2_hidden(sK0,sK3) | ~spl8_1),
% 1.56/0.59    inference(avatar_component_clause,[],[f34])).
% 1.56/0.59  fof(f61,plain,(
% 1.56/0.59    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) | ~spl8_4),
% 1.56/0.59    inference(avatar_component_clause,[],[f59])).
% 1.56/0.59  fof(f62,plain,(
% 1.56/0.59    spl8_4 | ~spl8_3),
% 1.56/0.59    inference(avatar_split_clause,[],[f53,f49,f59])).
% 1.56/0.59  fof(f49,plain,(
% 1.56/0.59    spl8_3 <=> r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.56/0.59  fof(f53,plain,(
% 1.56/0.59    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) | ~spl8_3),
% 1.56/0.59    inference(resolution,[],[f51,f31])).
% 1.56/0.59  fof(f31,plain,(
% 1.56/0.59    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.56/0.59    inference(equality_resolution,[],[f24])).
% 1.56/0.59  fof(f24,plain,(
% 1.56/0.59    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.56/0.59    inference(cnf_transformation,[],[f2])).
% 1.56/0.59  fof(f2,axiom,(
% 1.56/0.59    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.56/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.56/0.59  fof(f51,plain,(
% 1.56/0.59    r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl8_3),
% 1.56/0.59    inference(avatar_component_clause,[],[f49])).
% 1.56/0.59  fof(f52,plain,(
% 1.56/0.59    spl8_3 | ~spl8_2),
% 1.56/0.59    inference(avatar_split_clause,[],[f46,f41,f49])).
% 1.77/0.59  fof(f41,plain,(
% 1.77/0.59    spl8_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.77/0.59  fof(f46,plain,(
% 1.77/0.59    r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl8_2),
% 1.77/0.59    inference(subsumption_resolution,[],[f45,f18])).
% 1.77/0.59  fof(f18,plain,(
% 1.77/0.59    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.77/0.59    inference(cnf_transformation,[],[f5])).
% 1.77/0.59  fof(f5,axiom,(
% 1.77/0.59    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.77/0.59  fof(f45,plain,(
% 1.77/0.59    v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl8_2),
% 1.77/0.59    inference(resolution,[],[f43,f19])).
% 1.77/0.59  fof(f19,plain,(
% 1.77/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f12])).
% 1.77/0.59  fof(f12,plain,(
% 1.77/0.59    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.77/0.59    inference(flattening,[],[f11])).
% 1.77/0.59  fof(f11,plain,(
% 1.77/0.59    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.77/0.59    inference(ennf_transformation,[],[f6])).
% 1.77/0.59  fof(f6,axiom,(
% 1.77/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.77/0.59  fof(f43,plain,(
% 1.77/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl8_2),
% 1.77/0.59    inference(avatar_component_clause,[],[f41])).
% 1.77/0.59  fof(f44,plain,(
% 1.77/0.59    spl8_2),
% 1.77/0.59    inference(avatar_split_clause,[],[f16,f41])).
% 1.77/0.59  fof(f16,plain,(
% 1.77/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.77/0.59    inference(cnf_transformation,[],[f10])).
% 1.77/0.59  fof(f37,plain,(
% 1.77/0.59    spl8_1),
% 1.77/0.59    inference(avatar_split_clause,[],[f17,f34])).
% 1.77/0.59  fof(f17,plain,(
% 1.77/0.59    r2_hidden(sK0,sK3)),
% 1.77/0.59    inference(cnf_transformation,[],[f10])).
% 1.77/0.59  % SZS output end Proof for theBenchmark
% 1.77/0.59  % (19983)------------------------------
% 1.77/0.59  % (19983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.59  % (19983)Termination reason: Refutation
% 1.77/0.59  
% 1.77/0.59  % (19983)Memory used [KB]: 11001
% 1.77/0.59  % (19983)Time elapsed: 0.146 s
% 1.77/0.59  % (19983)------------------------------
% 1.77/0.59  % (19983)------------------------------
% 1.77/0.59  % (19962)Success in time 0.226 s
%------------------------------------------------------------------------------

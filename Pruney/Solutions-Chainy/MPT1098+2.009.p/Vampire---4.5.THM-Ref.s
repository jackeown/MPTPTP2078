%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:27 EST 2020

% Result     : Theorem 1.86s
% Output     : Refutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 135 expanded)
%              Number of leaves         :   15 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  171 ( 359 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1312,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f74,f91,f106,f112,f119,f167,f1261,f1276])).

fof(f1276,plain,
    ( ~ spl6_6
    | ~ spl6_8
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f1264,f1258,f88,f71])).

fof(f71,plain,
    ( spl6_6
  <=> v1_finset_1(sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f88,plain,
    ( spl6_8
  <=> r1_tarski(sK4(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f1258,plain,
    ( spl6_78
  <=> r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f1264,plain,
    ( ~ r1_tarski(sK4(sK0,sK1,sK2),sK1)
    | ~ v1_finset_1(sK4(sK0,sK1,sK2))
    | ~ spl6_78 ),
    inference(resolution,[],[f1260,f15])).

fof(f15,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
      | ~ r1_tarski(X3,sK1)
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
          | ~ r1_tarski(X3,X1)
          | ~ v1_finset_1(X3) )
      & r1_tarski(X0,k2_zfmisc_1(X1,X2))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ! [X3] :
              ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
                & r1_tarski(X3,X1)
                & v1_finset_1(X3) )
          & r1_tarski(X0,k2_zfmisc_1(X1,X2))
          & v1_finset_1(X0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ! [X3] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_finset_1)).

fof(f1260,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK2))
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f1258])).

fof(f1261,plain,
    ( spl6_78
    | ~ spl6_11
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f1245,f164,f109,f1258])).

fof(f109,plain,
    ( spl6_11
  <=> sK2 = k2_xboole_0(sK5(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f164,plain,
    ( spl6_18
  <=> k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)) = k2_xboole_0(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f1245,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK2))
    | ~ spl6_11
    | ~ spl6_18 ),
    inference(resolution,[],[f1099,f473])).

fof(f473,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)),X0)
        | r1_tarski(sK0,X0) )
    | ~ spl6_18 ),
    inference(superposition,[],[f22,f166])).

fof(f166,plain,
    ( k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)) = k2_xboole_0(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f164])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f1099,plain,
    ( ! [X10] : r1_tarski(k2_zfmisc_1(X10,sK5(sK0,sK1,sK2)),k2_zfmisc_1(X10,sK2))
    | ~ spl6_11 ),
    inference(superposition,[],[f1062,f111])).

fof(f111,plain,
    ( sK2 = k2_xboole_0(sK5(sK0,sK1,sK2),sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f1062,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f747,f47])).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f46,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f46,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f21,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f747,plain,(
    ! [X2,X0,X3,X1] : r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))) ),
    inference(resolution,[],[f463,f22])).

fof(f463,plain,(
    ! [X2,X0,X3,X1] : r1_tarski(k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),k2_zfmisc_1(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))) ),
    inference(resolution,[],[f126,f46])).

fof(f126,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | r1_tarski(k2_xboole_0(k2_zfmisc_1(X3,X4),X0),k2_zfmisc_1(k2_xboole_0(X3,X1),k2_xboole_0(X4,X2))) ) ),
    inference(resolution,[],[f28,f46])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X2,X3))
      | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5))
      | r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f167,plain,
    ( spl6_18
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f137,f116,f164])).

fof(f116,plain,
    ( spl6_12
  <=> r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f137,plain,
    ( k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)) = k2_xboole_0(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)))
    | ~ spl6_12 ),
    inference(resolution,[],[f118,f18])).

fof(f118,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f119,plain,
    ( spl6_12
    | ~ spl6_2
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f114,f30,f35,f116])).

fof(f35,plain,
    ( spl6_2
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f30,plain,
    ( spl6_1
  <=> r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f114,plain,
    ( ~ v1_finset_1(sK0)
    | r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)))
    | ~ spl6_1 ),
    inference(resolution,[],[f27,f32])).

fof(f32,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(sK4(X0,X1,X2),sK5(X0,X1,X2))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
              & r1_tarski(X4,X2)
              & v1_finset_1(X4)
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_finset_1)).

fof(f112,plain,
    ( spl6_11
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f107,f103,f109])).

fof(f103,plain,
    ( spl6_10
  <=> r1_tarski(sK5(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f107,plain,
    ( sK2 = k2_xboole_0(sK5(sK0,sK1,sK2),sK2)
    | ~ spl6_10 ),
    inference(resolution,[],[f105,f18])).

fof(f105,plain,
    ( r1_tarski(sK5(sK0,sK1,sK2),sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f106,plain,
    ( spl6_10
    | ~ spl6_2
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f100,f30,f35,f103])).

fof(f100,plain,
    ( ~ v1_finset_1(sK0)
    | r1_tarski(sK5(sK0,sK1,sK2),sK2)
    | ~ spl6_1 ),
    inference(resolution,[],[f26,f32])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0)
      | r1_tarski(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f91,plain,
    ( spl6_8
    | ~ spl6_2
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f85,f30,f35,f88])).

fof(f85,plain,
    ( ~ v1_finset_1(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),sK1)
    | ~ spl6_1 ),
    inference(resolution,[],[f24,f32])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0)
      | r1_tarski(sK4(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f74,plain,
    ( spl6_6
    | ~ spl6_2
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f68,f30,f35,f71])).

fof(f68,plain,
    ( ~ v1_finset_1(sK0)
    | v1_finset_1(sK4(sK0,sK1,sK2))
    | ~ spl6_1 ),
    inference(resolution,[],[f23,f32])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0)
      | v1_finset_1(sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f33,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (24412)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (24425)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (24407)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (24417)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (24421)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (24425)Refutation not found, incomplete strategy% (24425)------------------------------
% 0.20/0.51  % (24425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24425)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (24425)Memory used [KB]: 10618
% 0.20/0.51  % (24425)Time elapsed: 0.057 s
% 0.20/0.51  % (24425)------------------------------
% 0.20/0.51  % (24425)------------------------------
% 0.20/0.51  % (24409)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (24410)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (24429)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (24419)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (24424)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (24405)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (24403)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (24408)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (24426)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (24406)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (24430)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (24404)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (24432)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (24411)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (24431)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (24414)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (24422)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (24427)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (24416)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (24418)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (24423)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (24413)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (24428)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (24415)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (24420)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.86/0.59  % (24419)Refutation found. Thanks to Tanya!
% 1.86/0.59  % SZS status Theorem for theBenchmark
% 1.86/0.61  % SZS output start Proof for theBenchmark
% 1.86/0.61  fof(f1312,plain,(
% 1.86/0.61    $false),
% 1.86/0.61    inference(avatar_sat_refutation,[],[f33,f38,f74,f91,f106,f112,f119,f167,f1261,f1276])).
% 1.86/0.61  fof(f1276,plain,(
% 1.86/0.61    ~spl6_6 | ~spl6_8 | ~spl6_78),
% 1.86/0.61    inference(avatar_split_clause,[],[f1264,f1258,f88,f71])).
% 1.86/0.61  fof(f71,plain,(
% 1.86/0.61    spl6_6 <=> v1_finset_1(sK4(sK0,sK1,sK2))),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.86/0.61  fof(f88,plain,(
% 1.86/0.61    spl6_8 <=> r1_tarski(sK4(sK0,sK1,sK2),sK1)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.86/0.61  fof(f1258,plain,(
% 1.86/0.61    spl6_78 <=> r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK2))),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 1.86/0.61  fof(f1264,plain,(
% 1.86/0.61    ~r1_tarski(sK4(sK0,sK1,sK2),sK1) | ~v1_finset_1(sK4(sK0,sK1,sK2)) | ~spl6_78),
% 1.86/0.61    inference(resolution,[],[f1260,f15])).
% 1.86/0.61  fof(f15,plain,(
% 1.86/0.61    ( ! [X3] : (~r1_tarski(sK0,k2_zfmisc_1(X3,sK2)) | ~r1_tarski(X3,sK1) | ~v1_finset_1(X3)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f8])).
% 1.86/0.61  fof(f8,plain,(
% 1.86/0.61    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 1.86/0.61    inference(ennf_transformation,[],[f7])).
% 1.86/0.61  fof(f7,negated_conjecture,(
% 1.86/0.61    ~! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 1.86/0.61    inference(negated_conjecture,[],[f6])).
% 1.86/0.61  fof(f6,conjecture,(
% 1.86/0.61    ! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_finset_1)).
% 1.86/0.61  fof(f1260,plain,(
% 1.86/0.61    r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK2)) | ~spl6_78),
% 1.86/0.61    inference(avatar_component_clause,[],[f1258])).
% 1.86/0.61  fof(f1261,plain,(
% 1.86/0.61    spl6_78 | ~spl6_11 | ~spl6_18),
% 1.86/0.61    inference(avatar_split_clause,[],[f1245,f164,f109,f1258])).
% 1.86/0.61  fof(f109,plain,(
% 1.86/0.61    spl6_11 <=> sK2 = k2_xboole_0(sK5(sK0,sK1,sK2),sK2)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.86/0.61  fof(f164,plain,(
% 1.86/0.61    spl6_18 <=> k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)) = k2_xboole_0(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)))),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.86/0.61  fof(f1245,plain,(
% 1.86/0.61    r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK2)) | (~spl6_11 | ~spl6_18)),
% 1.86/0.61    inference(resolution,[],[f1099,f473])).
% 1.86/0.61  fof(f473,plain,(
% 1.86/0.61    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)),X0) | r1_tarski(sK0,X0)) ) | ~spl6_18),
% 1.86/0.61    inference(superposition,[],[f22,f166])).
% 1.86/0.61  fof(f166,plain,(
% 1.86/0.61    k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)) = k2_xboole_0(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2))) | ~spl6_18),
% 1.86/0.61    inference(avatar_component_clause,[],[f164])).
% 1.86/0.61  fof(f22,plain,(
% 1.86/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f11])).
% 1.86/0.61  fof(f11,plain,(
% 1.86/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.86/0.61    inference(ennf_transformation,[],[f2])).
% 1.86/0.61  fof(f2,axiom,(
% 1.86/0.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.86/0.61  fof(f1099,plain,(
% 1.86/0.61    ( ! [X10] : (r1_tarski(k2_zfmisc_1(X10,sK5(sK0,sK1,sK2)),k2_zfmisc_1(X10,sK2))) ) | ~spl6_11),
% 1.86/0.61    inference(superposition,[],[f1062,f111])).
% 1.86/0.61  fof(f111,plain,(
% 1.86/0.61    sK2 = k2_xboole_0(sK5(sK0,sK1,sK2),sK2) | ~spl6_11),
% 1.86/0.61    inference(avatar_component_clause,[],[f109])).
% 1.86/0.61  fof(f1062,plain,(
% 1.86/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k2_xboole_0(X1,X2)))) )),
% 1.86/0.61    inference(superposition,[],[f747,f47])).
% 1.86/0.61  fof(f47,plain,(
% 1.86/0.61    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.86/0.61    inference(resolution,[],[f46,f18])).
% 1.86/0.61  fof(f18,plain,(
% 1.86/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.86/0.61    inference(cnf_transformation,[],[f9])).
% 1.86/0.61  fof(f9,plain,(
% 1.86/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.86/0.61    inference(ennf_transformation,[],[f3])).
% 1.86/0.61  fof(f3,axiom,(
% 1.86/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.86/0.61  fof(f46,plain,(
% 1.86/0.61    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.86/0.61    inference(duplicate_literal_removal,[],[f45])).
% 1.86/0.61  fof(f45,plain,(
% 1.86/0.61    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.86/0.61    inference(resolution,[],[f21,f20])).
% 1.86/0.61  fof(f20,plain,(
% 1.86/0.61    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f10])).
% 1.86/0.61  fof(f10,plain,(
% 1.86/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.86/0.61    inference(ennf_transformation,[],[f1])).
% 1.86/0.61  fof(f1,axiom,(
% 1.86/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.86/0.61  fof(f21,plain,(
% 1.86/0.61    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f10])).
% 1.86/0.61  fof(f747,plain,(
% 1.86/0.61    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))) )),
% 1.86/0.61    inference(resolution,[],[f463,f22])).
% 1.86/0.61  fof(f463,plain,(
% 1.86/0.61    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),k2_zfmisc_1(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))) )),
% 1.86/0.61    inference(resolution,[],[f126,f46])).
% 1.86/0.61  fof(f126,plain,(
% 1.86/0.61    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | r1_tarski(k2_xboole_0(k2_zfmisc_1(X3,X4),X0),k2_zfmisc_1(k2_xboole_0(X3,X1),k2_xboole_0(X4,X2)))) )),
% 1.86/0.61    inference(resolution,[],[f28,f46])).
% 1.86/0.61  fof(f28,plain,(
% 1.86/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tarski(X0,k2_zfmisc_1(X2,X3)) | ~r1_tarski(X1,k2_zfmisc_1(X4,X5)) | r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))) )),
% 1.86/0.61    inference(cnf_transformation,[],[f14])).
% 1.86/0.61  fof(f14,plain,(
% 1.86/0.61    ! [X0,X1,X2,X3,X4,X5] : (r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) | ~r1_tarski(X1,k2_zfmisc_1(X4,X5)) | ~r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 1.86/0.61    inference(flattening,[],[f13])).
% 1.86/0.61  fof(f13,plain,(
% 1.86/0.61    ! [X0,X1,X2,X3,X4,X5] : (r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) | (~r1_tarski(X1,k2_zfmisc_1(X4,X5)) | ~r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 1.86/0.61    inference(ennf_transformation,[],[f4])).
% 1.86/0.61  fof(f4,axiom,(
% 1.86/0.61    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 1.86/0.61  fof(f167,plain,(
% 1.86/0.61    spl6_18 | ~spl6_12),
% 1.86/0.61    inference(avatar_split_clause,[],[f137,f116,f164])).
% 1.86/0.61  fof(f116,plain,(
% 1.86/0.61    spl6_12 <=> r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)))),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.86/0.61  fof(f137,plain,(
% 1.86/0.61    k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2)) = k2_xboole_0(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2))) | ~spl6_12),
% 1.86/0.61    inference(resolution,[],[f118,f18])).
% 1.86/0.61  fof(f118,plain,(
% 1.86/0.61    r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2))) | ~spl6_12),
% 1.86/0.61    inference(avatar_component_clause,[],[f116])).
% 1.86/0.61  fof(f119,plain,(
% 1.86/0.61    spl6_12 | ~spl6_2 | ~spl6_1),
% 1.86/0.61    inference(avatar_split_clause,[],[f114,f30,f35,f116])).
% 1.86/0.61  fof(f35,plain,(
% 1.86/0.61    spl6_2 <=> v1_finset_1(sK0)),
% 1.86/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.86/0.62  fof(f30,plain,(
% 1.86/0.62    spl6_1 <=> r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.86/0.62  fof(f114,plain,(
% 1.86/0.62    ~v1_finset_1(sK0) | r1_tarski(sK0,k2_zfmisc_1(sK4(sK0,sK1,sK2),sK5(sK0,sK1,sK2))) | ~spl6_1),
% 1.86/0.62    inference(resolution,[],[f27,f32])).
% 1.86/0.62  fof(f32,plain,(
% 1.86/0.62    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) | ~spl6_1),
% 1.86/0.62    inference(avatar_component_clause,[],[f30])).
% 1.86/0.62  fof(f27,plain,(
% 1.86/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0) | r1_tarski(X0,k2_zfmisc_1(sK4(X0,X1,X2),sK5(X0,X1,X2)))) )),
% 1.86/0.62    inference(cnf_transformation,[],[f12])).
% 1.86/0.62  fof(f12,plain,(
% 1.86/0.62    ! [X0,X1,X2] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 1.86/0.62    inference(ennf_transformation,[],[f5])).
% 1.86/0.62  fof(f5,axiom,(
% 1.86/0.62    ! [X0,X1,X2] : ~(! [X3,X4] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_finset_1)).
% 1.86/0.62  fof(f112,plain,(
% 1.86/0.62    spl6_11 | ~spl6_10),
% 1.86/0.62    inference(avatar_split_clause,[],[f107,f103,f109])).
% 1.86/0.62  fof(f103,plain,(
% 1.86/0.62    spl6_10 <=> r1_tarski(sK5(sK0,sK1,sK2),sK2)),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.86/0.62  fof(f107,plain,(
% 1.86/0.62    sK2 = k2_xboole_0(sK5(sK0,sK1,sK2),sK2) | ~spl6_10),
% 1.86/0.62    inference(resolution,[],[f105,f18])).
% 1.86/0.62  fof(f105,plain,(
% 1.86/0.62    r1_tarski(sK5(sK0,sK1,sK2),sK2) | ~spl6_10),
% 1.86/0.62    inference(avatar_component_clause,[],[f103])).
% 1.86/0.62  fof(f106,plain,(
% 1.86/0.62    spl6_10 | ~spl6_2 | ~spl6_1),
% 1.86/0.62    inference(avatar_split_clause,[],[f100,f30,f35,f103])).
% 1.86/0.62  fof(f100,plain,(
% 1.86/0.62    ~v1_finset_1(sK0) | r1_tarski(sK5(sK0,sK1,sK2),sK2) | ~spl6_1),
% 1.86/0.62    inference(resolution,[],[f26,f32])).
% 1.86/0.62  fof(f26,plain,(
% 1.86/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0) | r1_tarski(sK5(X0,X1,X2),X2)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f12])).
% 1.86/0.62  fof(f91,plain,(
% 1.86/0.62    spl6_8 | ~spl6_2 | ~spl6_1),
% 1.86/0.62    inference(avatar_split_clause,[],[f85,f30,f35,f88])).
% 1.86/0.62  fof(f85,plain,(
% 1.86/0.62    ~v1_finset_1(sK0) | r1_tarski(sK4(sK0,sK1,sK2),sK1) | ~spl6_1),
% 1.86/0.62    inference(resolution,[],[f24,f32])).
% 1.86/0.62  fof(f24,plain,(
% 1.86/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0) | r1_tarski(sK4(X0,X1,X2),X1)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f12])).
% 1.86/0.62  fof(f74,plain,(
% 1.86/0.62    spl6_6 | ~spl6_2 | ~spl6_1),
% 1.86/0.62    inference(avatar_split_clause,[],[f68,f30,f35,f71])).
% 1.86/0.62  fof(f68,plain,(
% 1.86/0.62    ~v1_finset_1(sK0) | v1_finset_1(sK4(sK0,sK1,sK2)) | ~spl6_1),
% 1.86/0.62    inference(resolution,[],[f23,f32])).
% 1.86/0.62  fof(f23,plain,(
% 1.86/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0) | v1_finset_1(sK4(X0,X1,X2))) )),
% 1.86/0.62    inference(cnf_transformation,[],[f12])).
% 1.86/0.62  fof(f38,plain,(
% 1.86/0.62    spl6_2),
% 1.86/0.62    inference(avatar_split_clause,[],[f16,f35])).
% 1.86/0.62  fof(f16,plain,(
% 1.86/0.62    v1_finset_1(sK0)),
% 1.86/0.62    inference(cnf_transformation,[],[f8])).
% 1.86/0.62  fof(f33,plain,(
% 1.86/0.62    spl6_1),
% 1.86/0.62    inference(avatar_split_clause,[],[f17,f30])).
% 1.86/0.62  fof(f17,plain,(
% 1.86/0.62    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))),
% 1.86/0.62    inference(cnf_transformation,[],[f8])).
% 1.86/0.62  % SZS output end Proof for theBenchmark
% 1.86/0.62  % (24419)------------------------------
% 1.86/0.62  % (24419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.86/0.62  % (24419)Termination reason: Refutation
% 1.86/0.62  
% 1.86/0.62  % (24419)Memory used [KB]: 11641
% 1.86/0.62  % (24419)Time elapsed: 0.200 s
% 1.86/0.62  % (24419)------------------------------
% 1.86/0.62  % (24419)------------------------------
% 1.86/0.62  % (24402)Success in time 0.27 s
%------------------------------------------------------------------------------

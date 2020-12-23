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
% DateTime   : Thu Dec  3 13:13:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 101 expanded)
%              Number of leaves         :   19 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :  158 ( 256 expanded)
%              Number of equality atoms :   26 (  47 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f58,f63,f68,f74,f84,f97,f102,f117])).

fof(f117,plain,
    ( spl3_2
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f106,f90,f60,f40,f45])).

fof(f45,plain,
    ( spl3_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f40,plain,
    ( spl3_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f60,plain,
    ( spl3_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f90,plain,
    ( spl3_9
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f106,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(superposition,[],[f27,f92])).

fof(f92,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f90])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f102,plain,(
    ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | ~ spl3_10 ),
    inference(resolution,[],[f96,f75])).

fof(f75,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f31,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f31,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f96,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0)),k1_xboole_0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_10
  <=> r2_hidden(sK2(u1_struct_0(sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f97,plain,
    ( spl3_9
    | spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f88,f81,f94,f90])).

fof(f81,plain,
    ( spl3_8
  <=> r1_tarski(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f88,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0)),k1_xboole_0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f85,f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f85,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl3_8 ),
    inference(resolution,[],[f32,f83])).

fof(f83,plain,
    ( r1_tarski(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f81])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f84,plain,
    ( spl3_8
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f79,f71,f65,f81])).

fof(f65,plain,
    ( spl3_6
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f71,plain,
    ( spl3_7
  <=> m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f79,plain,
    ( r1_tarski(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f78,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f78,plain,
    ( r1_tarski(u1_struct_0(sK0),k3_tarski(k1_xboole_0))
    | ~ spl3_7 ),
    inference(resolution,[],[f33,f73])).

fof(f73,plain,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(X1,X0)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f74,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f69,f55,f50,f71])).

fof(f50,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f55,plain,
    ( spl3_4
  <=> m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f69,plain,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f57,f52])).

% (24718)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f52,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f57,plain,
    ( m1_setfam_1(sK1,u1_struct_0(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f68,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f26,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f63,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f58,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f55])).

fof(f21,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

fof(f53,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f24,f40])).

fof(f24,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:26:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (24709)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (24698)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (24705)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (24705)Refutation not found, incomplete strategy% (24705)------------------------------
% 0.21/0.50  % (24705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24725)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.50  % (24698)Refutation not found, incomplete strategy% (24698)------------------------------
% 0.21/0.50  % (24698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24705)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (24705)Memory used [KB]: 10618
% 0.21/0.50  % (24705)Time elapsed: 0.093 s
% 0.21/0.50  % (24705)------------------------------
% 0.21/0.50  % (24705)------------------------------
% 0.21/0.51  % (24698)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24698)Memory used [KB]: 10618
% 0.21/0.51  % (24698)Time elapsed: 0.094 s
% 0.21/0.51  % (24698)------------------------------
% 0.21/0.51  % (24698)------------------------------
% 0.21/0.51  % (24712)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (24712)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f43,f48,f53,f58,f63,f68,f74,f84,f97,f102,f117])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    spl3_2 | ~spl3_1 | ~spl3_5 | ~spl3_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f106,f90,f60,f40,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    spl3_2 <=> v2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    spl3_1 <=> l1_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    spl3_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl3_9 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_9),
% 0.21/0.51    inference(superposition,[],[f27,f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    k1_xboole_0 = u1_struct_0(sK0) | ~spl3_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ~spl3_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    $false | ~spl3_10),
% 0.21/0.51    inference(resolution,[],[f96,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(superposition,[],[f31,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    r2_hidden(sK2(u1_struct_0(sK0)),k1_xboole_0) | ~spl3_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl3_10 <=> r2_hidden(sK2(u1_struct_0(sK0)),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl3_9 | spl3_10 | ~spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f88,f81,f94,f90])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    spl3_8 <=> r1_tarski(u1_struct_0(sK0),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    r2_hidden(sK2(u1_struct_0(sK0)),k1_xboole_0) | k1_xboole_0 = u1_struct_0(sK0) | ~spl3_8),
% 0.21/0.51    inference(resolution,[],[f85,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK0)) | r2_hidden(X0,k1_xboole_0)) ) | ~spl3_8),
% 0.21/0.51    inference(resolution,[],[f32,f83])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    r1_tarski(u1_struct_0(sK0),k1_xboole_0) | ~spl3_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f81])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.51    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl3_8 | ~spl3_6 | ~spl3_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f79,f71,f65,f81])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    spl3_6 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    spl3_7 <=> m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    r1_tarski(u1_struct_0(sK0),k1_xboole_0) | (~spl3_6 | ~spl3_7)),
% 0.21/0.51    inference(forward_demodulation,[],[f78,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    k1_xboole_0 = k3_tarski(k1_xboole_0) | ~spl3_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f65])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    r1_tarski(u1_struct_0(sK0),k3_tarski(k1_xboole_0)) | ~spl3_7),
% 0.21/0.51    inference(resolution,[],[f33,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) | ~spl3_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f71])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_setfam_1(X1,X0) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_setfam_1(X1,X0) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.51    inference(unused_predicate_definition_removal,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    spl3_7 | ~spl3_3 | ~spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f69,f55,f50,f71])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    spl3_3 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    spl3_4 <=> m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) | (~spl3_3 | ~spl3_4)),
% 0.21/0.51    inference(forward_demodulation,[],[f57,f52])).
% 0.21/0.51  % (24718)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl3_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f50])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    m1_setfam_1(sK1,u1_struct_0(sK0)) | ~spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f55])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f26,f65])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f25,f60])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f21,f55])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f22,f50])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    k1_xboole_0 = sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f23,f45])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f24,f40])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    l1_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (24712)------------------------------
% 0.21/0.51  % (24712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24712)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (24712)Memory used [KB]: 10746
% 0.21/0.51  % (24712)Time elapsed: 0.108 s
% 0.21/0.51  % (24712)------------------------------
% 0.21/0.51  % (24712)------------------------------
% 0.21/0.51  % (24718)Refutation not found, incomplete strategy% (24718)------------------------------
% 0.21/0.51  % (24718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24718)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24718)Memory used [KB]: 10618
% 0.21/0.51  % (24718)Time elapsed: 0.064 s
% 0.21/0.51  % (24718)------------------------------
% 0.21/0.51  % (24718)------------------------------
% 0.21/0.52  % (24695)Success in time 0.158 s
%------------------------------------------------------------------------------

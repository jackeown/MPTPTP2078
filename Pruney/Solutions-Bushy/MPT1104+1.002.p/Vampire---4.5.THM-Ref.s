%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1104+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 188 expanded)
%              Number of leaves         :   27 (  88 expanded)
%              Depth                    :    9
%              Number of atoms          :  271 ( 669 expanded)
%              Number of equality atoms :   66 ( 211 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (24068)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f269,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f47,f51,f55,f59,f63,f68,f84,f88,f106,f124,f137,f174,f191,f265,f268])).

fof(f268,plain,
    ( ~ spl3_14
    | spl3_16 ),
    inference(avatar_split_clause,[],[f267,f120,f111])).

fof(f111,plain,
    ( spl3_14
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f120,plain,
    ( spl3_16
  <=> sK2 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f267,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl3_16 ),
    inference(trivial_inequality_removal,[],[f266])).

fof(f266,plain,
    ( sK2 != sK2
    | ~ r1_xboole_0(sK2,sK1)
    | spl3_16 ),
    inference(superposition,[],[f121,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f121,plain,
    ( sK2 != k4_xboole_0(sK2,sK1)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f120])).

fof(f265,plain,
    ( ~ spl3_16
    | spl3_12
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f261,f189,f101,f120])).

fof(f101,plain,
    ( spl3_12
  <=> sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f189,plain,
    ( spl3_19
  <=> k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f261,plain,
    ( sK2 != k4_xboole_0(sK2,sK1)
    | spl3_12
    | ~ spl3_19 ),
    inference(superposition,[],[f102,f190])).

fof(f190,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f189])).

fof(f102,plain,
    ( sK2 != k4_xboole_0(k2_struct_0(sK0),sK1)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f191,plain,
    ( spl3_19
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f177,f168,f189])).

fof(f168,plain,
    ( spl3_17
  <=> k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f177,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,sK1)
    | ~ spl3_17 ),
    inference(superposition,[],[f89,f169])).

fof(f169,plain,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f168])).

fof(f89,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f33,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f174,plain,
    ( spl3_17
    | ~ spl3_11
    | ~ spl3_10
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f173,f66,f49,f82,f86,f168])).

fof(f86,plain,
    ( spl3_11
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f82,plain,
    ( spl3_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f49,plain,
    ( spl3_3
  <=> k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f66,plain,
    ( spl3_7
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f173,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f172,f67])).

fof(f67,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f172,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f161,f67])).

fof(f161,plain,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(superposition,[],[f50,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

% (24067)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f50,plain,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f137,plain,
    ( spl3_13
    | ~ spl3_11
    | ~ spl3_10
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f133,f66,f49,f82,f86,f104])).

fof(f104,plain,
    ( spl3_13
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f133,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f132,f67])).

fof(f132,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f131,f67])).

fof(f131,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f129,f67])).

fof(f129,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(superposition,[],[f38,f50])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

% (24068)Refutation not found, incomplete strategy% (24068)------------------------------
% (24068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24068)Termination reason: Refutation not found, incomplete strategy

% (24068)Memory used [KB]: 10618
% (24068)Time elapsed: 0.090 s
% (24068)------------------------------
% (24068)------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f124,plain,
    ( ~ spl3_2
    | spl3_14 ),
    inference(avatar_split_clause,[],[f118,f111,f45])).

fof(f45,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f118,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl3_14 ),
    inference(resolution,[],[f112,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f112,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f111])).

fof(f106,plain,
    ( ~ spl3_12
    | ~ spl3_13
    | spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f99,f66,f41,f104,f101])).

fof(f41,plain,
    ( spl3_1
  <=> k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f99,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | sK2 != k4_xboole_0(k2_struct_0(sK0),sK1)
    | spl3_1
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f97,f67])).

fof(f97,plain,
    ( sK2 != k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1 ),
    inference(superposition,[],[f42,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f42,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2
    | spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f88,plain,
    ( spl3_11
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f75,f66,f53,f86])).

fof(f53,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f75,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(superposition,[],[f54,f67])).

fof(f54,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f84,plain,
    ( spl3_10
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f74,f66,f57,f82])).

fof(f57,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f74,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(superposition,[],[f58,f67])).

fof(f58,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f68,plain,
    ( spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f64,f61,f66])).

fof(f61,plain,
    ( spl3_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f64,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f31,f62])).

fof(f62,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f31,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f63,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f25,f61])).

fof(f25,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2
    & r1_xboole_0(sK1,sK2)
    & k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
                & r1_xboole_0(X1,X2)
                & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) != X2
              & r1_xboole_0(X1,X2)
              & k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) != X2
            & r1_xboole_0(X1,X2)
            & k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2
          & r1_xboole_0(sK1,X2)
          & k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2
        & r1_xboole_0(sK1,X2)
        & k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2
      & r1_xboole_0(sK1,sK2)
      & k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
              & r1_xboole_0(X1,X2)
              & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
              & r1_xboole_0(X1,X2)
              & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_xboole_0(X1,X2)
                    & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2) )
                 => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_xboole_0(X1,X2)
                  & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2) )
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_pre_topc)).

fof(f59,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f26,f57])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f27,f53])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f28,f49])).

fof(f28,plain,(
    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f29,f45])).

fof(f29,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f30,f41])).

fof(f30,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------

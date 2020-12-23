%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 133 expanded)
%              Number of leaves         :   25 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :  225 ( 424 expanded)
%              Number of equality atoms :   25 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f190,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f61,f66,f71,f76,f81,f88,f101,f109,f136,f149,f166,f189])).

fof(f189,plain,
    ( ~ spl3_8
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl3_8
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f170,f148])).

fof(f148,plain,
    ( r2_hidden(sK2(k1_xboole_0,u1_struct_0(sK0)),k1_xboole_0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_17
  <=> r2_hidden(sK2(k1_xboole_0,u1_struct_0(sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f170,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0,u1_struct_0(sK0)),k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f80,f148,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f80,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_8
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f166,plain,
    ( k1_xboole_0 != u1_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f149,plain,
    ( spl3_17
    | spl3_15 ),
    inference(avatar_split_clause,[],[f144,f133,f146])).

fof(f133,plain,
    ( spl3_15
  <=> r1_xboole_0(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f144,plain,
    ( r2_hidden(sK2(k1_xboole_0,u1_struct_0(sK0)),k1_xboole_0)
    | spl3_15 ),
    inference(unit_resulting_resolution,[],[f135,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f135,plain,
    ( ~ r1_xboole_0(k1_xboole_0,u1_struct_0(sK0))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f133])).

fof(f136,plain,
    ( spl3_14
    | ~ spl3_15
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f127,f106,f133,f129])).

fof(f129,plain,
    ( spl3_14
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f106,plain,
    ( spl3_12
  <=> r1_tarski(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f127,plain,
    ( ~ r1_xboole_0(k1_xboole_0,u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl3_12 ),
    inference(resolution,[],[f120,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f120,plain,
    ( ! [X3] :
        ( r1_xboole_0(u1_struct_0(sK0),X3)
        | ~ r1_xboole_0(k1_xboole_0,X3) )
    | ~ spl3_12 ),
    inference(resolution,[],[f40,f108])).

fof(f108,plain,
    ( r1_tarski(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f109,plain,
    ( spl3_12
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f104,f85,f73,f106])).

fof(f73,plain,
    ( spl3_7
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f85,plain,
    ( spl3_9
  <=> m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f104,plain,
    ( r1_tarski(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f102,f75])).

fof(f75,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f102,plain,
    ( r1_tarski(u1_struct_0(sK0),k3_tarski(k1_xboole_0))
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f87,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f87,plain,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f101,plain,
    ( ~ spl3_11
    | ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f96,f63,f58,f98])).

fof(f98,plain,
    ( spl3_11
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f58,plain,
    ( spl3_4
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f63,plain,
    ( spl3_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f96,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_4
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f65,f60,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f60,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f65,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f88,plain,
    ( spl3_9
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f82,f48,f43,f85])).

fof(f43,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f48,plain,
    ( spl3_2
  <=> m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f82,plain,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f50,f45])).

fof(f45,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f50,plain,
    ( m1_setfam_1(sK1,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f81,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f41,f78])).

fof(f41,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f76,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f31,f73])).

fof(f31,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f71,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f30,f68])).

fof(f68,plain,
    ( spl3_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f66,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f25,f63])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 = sK1
    & m1_setfam_1(sK1,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = X1
            & m1_setfam_1(X1,u1_struct_0(X0))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(sK0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( k1_xboole_0 = X1
        & m1_setfam_1(X1,u1_struct_0(sK0))
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK1
      & m1_setfam_1(sK1,u1_struct_0(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

fof(f61,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f28,f48])).

fof(f28,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f29,f43])).

fof(f29,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (28917)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.44  % (28917)Refutation not found, incomplete strategy% (28917)------------------------------
% 0.21/0.44  % (28917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (28933)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.45  % (28917)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (28917)Memory used [KB]: 10490
% 0.21/0.45  % (28917)Time elapsed: 0.055 s
% 0.21/0.45  % (28917)------------------------------
% 0.21/0.45  % (28917)------------------------------
% 0.21/0.45  % (28928)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.45  % (28924)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (28933)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f190,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f46,f51,f61,f66,f71,f76,f81,f88,f101,f109,f136,f149,f166,f189])).
% 0.21/0.46  fof(f189,plain,(
% 0.21/0.46    ~spl3_8 | ~spl3_17),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f188])).
% 0.21/0.46  fof(f188,plain,(
% 0.21/0.46    $false | (~spl3_8 | ~spl3_17)),
% 0.21/0.46    inference(subsumption_resolution,[],[f170,f148])).
% 0.21/0.46  fof(f148,plain,(
% 0.21/0.46    r2_hidden(sK2(k1_xboole_0,u1_struct_0(sK0)),k1_xboole_0) | ~spl3_17),
% 0.21/0.46    inference(avatar_component_clause,[],[f146])).
% 0.21/0.46  fof(f146,plain,(
% 0.21/0.46    spl3_17 <=> r2_hidden(sK2(k1_xboole_0,u1_struct_0(sK0)),k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.46  fof(f170,plain,(
% 0.21/0.46    ~r2_hidden(sK2(k1_xboole_0,u1_struct_0(sK0)),k1_xboole_0) | (~spl3_8 | ~spl3_17)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f80,f148,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.46    inference(rectify,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f78])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    spl3_8 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.46  fof(f166,plain,(
% 0.21/0.46    k1_xboole_0 != u1_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.46  fof(f149,plain,(
% 0.21/0.46    spl3_17 | spl3_15),
% 0.21/0.46    inference(avatar_split_clause,[],[f144,f133,f146])).
% 0.21/0.46  fof(f133,plain,(
% 0.21/0.46    spl3_15 <=> r1_xboole_0(k1_xboole_0,u1_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.46  fof(f144,plain,(
% 0.21/0.46    r2_hidden(sK2(k1_xboole_0,u1_struct_0(sK0)),k1_xboole_0) | spl3_15),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f135,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    ~r1_xboole_0(k1_xboole_0,u1_struct_0(sK0)) | spl3_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f133])).
% 0.21/0.46  fof(f136,plain,(
% 0.21/0.46    spl3_14 | ~spl3_15 | ~spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f127,f106,f133,f129])).
% 0.21/0.46  fof(f129,plain,(
% 0.21/0.46    spl3_14 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    spl3_12 <=> r1_tarski(u1_struct_0(sK0),k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    ~r1_xboole_0(k1_xboole_0,u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0) | ~spl3_12),
% 0.21/0.46    inference(resolution,[],[f120,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    ( ! [X3] : (r1_xboole_0(u1_struct_0(sK0),X3) | ~r1_xboole_0(k1_xboole_0,X3)) ) | ~spl3_12),
% 0.21/0.46    inference(resolution,[],[f40,f108])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    r1_tarski(u1_struct_0(sK0),k1_xboole_0) | ~spl3_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f106])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    spl3_12 | ~spl3_7 | ~spl3_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f104,f85,f73,f106])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    spl3_7 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    spl3_9 <=> m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    r1_tarski(u1_struct_0(sK0),k1_xboole_0) | (~spl3_7 | ~spl3_9)),
% 0.21/0.46    inference(forward_demodulation,[],[f102,f75])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    k1_xboole_0 = k3_tarski(k1_xboole_0) | ~spl3_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f73])).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    r1_tarski(u1_struct_0(sK0),k3_tarski(k1_xboole_0)) | ~spl3_9),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f87,f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 0.21/0.46    inference(nnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) | ~spl3_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f85])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    ~spl3_11 | ~spl3_4 | spl3_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f96,f63,f58,f98])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    spl3_11 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    spl3_4 <=> l1_struct_0(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    spl3_5 <=> v2_struct_0(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    ~v1_xboole_0(u1_struct_0(sK0)) | (~spl3_4 | spl3_5)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f65,f60,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    l1_struct_0(sK0) | ~spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f58])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ~v2_struct_0(sK0) | spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f63])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    spl3_9 | ~spl3_1 | ~spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f82,f48,f43,f85])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    spl3_1 <=> k1_xboole_0 = sK1),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    spl3_2 <=> m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) | (~spl3_1 | ~spl3_2)),
% 0.21/0.46    inference(backward_demodulation,[],[f50,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    k1_xboole_0 = sK1 | ~spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f43])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    m1_setfam_1(sK1,u1_struct_0(sK0)) | ~spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f48])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    spl3_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f41,f78])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.46    inference(equality_resolution,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    spl3_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f31,f73])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    spl3_6 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ~spl3_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f63])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ~v2_struct_0(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f20,f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : ((k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.21/0.46    inference(negated_conjecture,[],[f8])).
% 0.21/0.46  fof(f8,conjecture,(
% 0.21/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    spl3_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f26,f58])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    l1_struct_0(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f28,f48])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f29,f43])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    k1_xboole_0 = sK1),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (28933)------------------------------
% 0.21/0.46  % (28933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (28933)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (28933)Memory used [KB]: 10746
% 0.21/0.46  % (28933)Time elapsed: 0.069 s
% 0.21/0.46  % (28933)------------------------------
% 0.21/0.46  % (28933)------------------------------
% 0.21/0.46  % (28914)Success in time 0.108 s
%------------------------------------------------------------------------------

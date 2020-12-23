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
% DateTime   : Thu Dec  3 12:56:12 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 159 expanded)
%              Number of leaves         :   19 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 253 expanded)
%              Number of equality atoms :   22 (  86 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f71,f77,f87,f91,f97])).

fof(f97,plain,
    ( ~ spl5_2
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl5_2
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f59,f59,f86,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f32,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

% (9029)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f86,plain,
    ( ~ r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_7
  <=> r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f59,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f91,plain,
    ( ~ spl5_1
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl5_1
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f54,f54,f82,f44])).

fof(f82,plain,
    ( ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_6
  <=> r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f54,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl5_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f87,plain,
    ( ~ spl5_6
    | ~ spl5_7
    | spl5_5 ),
    inference(avatar_split_clause,[],[f78,f74,f84,f80])).

fof(f74,plain,
    ( spl5_5
  <=> r1_tarski(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k2_zfmisc_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f78,plain,
    ( ~ r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)
    | ~ r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | spl5_5 ),
    inference(resolution,[],[f76,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f76,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k2_zfmisc_1(sK1,sK3))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f77,plain,
    ( ~ spl5_5
    | spl5_4 ),
    inference(avatar_split_clause,[],[f72,f68,f74])).

fof(f68,plain,
    ( spl5_4
  <=> r2_hidden(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

% (9019)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f72,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k2_zfmisc_1(sK1,sK3))
    | spl5_4 ),
    inference(resolution,[],[f70,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f70,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f71,plain,
    ( ~ spl5_4
    | spl5_3 ),
    inference(avatar_split_clause,[],[f66,f62,f68])).

fof(f62,plain,
    ( spl5_3
  <=> m1_subset_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f66,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | spl5_3 ),
    inference(resolution,[],[f64,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f64,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f65,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f50,f62])).

fof(f50,plain,(
    ~ m1_subset_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(forward_demodulation,[],[f43,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X3)) = k5_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(definition_unfolding,[],[f34,f41,f41,f39])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f43,plain,(
    ~ m1_subset_1(k5_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(definition_unfolding,[],[f21,f42])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f41])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f15])).

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

% (9021)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
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

fof(f60,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f20,f57])).

fof(f20,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f19,f52])).

fof(f19,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:19:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.32/0.53  % (9017)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.53  % (9025)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.54  % (9005)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.54  % (9005)Refutation not found, incomplete strategy% (9005)------------------------------
% 1.32/0.54  % (9005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (9005)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (9005)Memory used [KB]: 10618
% 1.32/0.54  % (9005)Time elapsed: 0.124 s
% 1.32/0.54  % (9005)------------------------------
% 1.32/0.54  % (9005)------------------------------
% 1.32/0.54  % (9027)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.54  % (9006)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.54  % (9008)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.54  % (9025)Refutation found. Thanks to Tanya!
% 1.32/0.54  % SZS status Theorem for theBenchmark
% 1.32/0.54  % (9007)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.54  % (9009)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.32/0.54  % SZS output start Proof for theBenchmark
% 1.32/0.54  fof(f98,plain,(
% 1.32/0.54    $false),
% 1.32/0.54    inference(avatar_sat_refutation,[],[f55,f60,f65,f71,f77,f87,f91,f97])).
% 1.32/0.54  fof(f97,plain,(
% 1.32/0.54    ~spl5_2 | spl5_7),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f94])).
% 1.32/0.54  fof(f94,plain,(
% 1.32/0.54    $false | (~spl5_2 | spl5_7)),
% 1.32/0.54    inference(unit_resulting_resolution,[],[f59,f59,f86,f44])).
% 1.32/0.54  fof(f44,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f32,f41])).
% 1.32/0.54  fof(f41,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f23,f40])).
% 1.32/0.54  fof(f40,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f29,f39])).
% 1.32/0.54  fof(f39,plain,(
% 1.32/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f33,f38])).
% 1.32/0.54  fof(f38,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f36,f37])).
% 1.32/0.54  fof(f37,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f6])).
% 1.32/0.54  fof(f6,axiom,(
% 1.32/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.32/0.54  fof(f36,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f5])).
% 1.32/0.54  fof(f5,axiom,(
% 1.32/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.32/0.54  fof(f33,plain,(
% 1.32/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f4])).
% 1.32/0.54  fof(f4,axiom,(
% 1.32/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.32/0.54  fof(f29,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f3])).
% 1.32/0.54  fof(f3,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.54  fof(f23,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f2])).
% 1.32/0.54  fof(f2,axiom,(
% 1.32/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.54  fof(f32,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f10])).
% 1.32/0.54  % (9029)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.54  fof(f10,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.32/0.54  fof(f86,plain,(
% 1.32/0.54    ~r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) | spl5_7),
% 1.32/0.54    inference(avatar_component_clause,[],[f84])).
% 1.32/0.54  fof(f84,plain,(
% 1.32/0.54    spl5_7 <=> r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.32/0.54  fof(f59,plain,(
% 1.32/0.54    r2_hidden(sK2,sK3) | ~spl5_2),
% 1.32/0.54    inference(avatar_component_clause,[],[f57])).
% 1.32/0.54  fof(f57,plain,(
% 1.32/0.54    spl5_2 <=> r2_hidden(sK2,sK3)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.32/0.54  fof(f91,plain,(
% 1.32/0.54    ~spl5_1 | spl5_6),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f88])).
% 1.32/0.54  fof(f88,plain,(
% 1.32/0.54    $false | (~spl5_1 | spl5_6)),
% 1.32/0.54    inference(unit_resulting_resolution,[],[f54,f54,f82,f44])).
% 1.32/0.54  fof(f82,plain,(
% 1.32/0.54    ~r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | spl5_6),
% 1.32/0.54    inference(avatar_component_clause,[],[f80])).
% 1.32/0.54  fof(f80,plain,(
% 1.32/0.54    spl5_6 <=> r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.32/0.54  fof(f54,plain,(
% 1.32/0.54    r2_hidden(sK0,sK1) | ~spl5_1),
% 1.32/0.54    inference(avatar_component_clause,[],[f52])).
% 1.32/0.54  fof(f52,plain,(
% 1.32/0.54    spl5_1 <=> r2_hidden(sK0,sK1)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.32/0.54  fof(f87,plain,(
% 1.32/0.54    ~spl5_6 | ~spl5_7 | spl5_5),
% 1.32/0.54    inference(avatar_split_clause,[],[f78,f74,f84,f80])).
% 1.32/0.54  fof(f74,plain,(
% 1.32/0.54    spl5_5 <=> r1_tarski(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k2_zfmisc_1(sK1,sK3))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.32/0.54  fof(f78,plain,(
% 1.32/0.54    ~r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) | ~r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | spl5_5),
% 1.32/0.54    inference(resolution,[],[f76,f35])).
% 1.32/0.54  fof(f35,plain,(
% 1.32/0.54    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f18])).
% 1.32/0.54  fof(f18,plain,(
% 1.32/0.54    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 1.32/0.54    inference(flattening,[],[f17])).
% 1.32/0.54  fof(f17,plain,(
% 1.32/0.54    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 1.32/0.54    inference(ennf_transformation,[],[f8])).
% 1.32/0.54  fof(f8,axiom,(
% 1.32/0.54    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).
% 1.32/0.54  fof(f76,plain,(
% 1.32/0.54    ~r1_tarski(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k2_zfmisc_1(sK1,sK3)) | spl5_5),
% 1.32/0.54    inference(avatar_component_clause,[],[f74])).
% 1.32/0.54  fof(f77,plain,(
% 1.32/0.54    ~spl5_5 | spl5_4),
% 1.32/0.54    inference(avatar_split_clause,[],[f72,f68,f74])).
% 1.32/0.54  fof(f68,plain,(
% 1.32/0.54    spl5_4 <=> r2_hidden(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.32/0.54  % (9019)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.32/0.54  fof(f72,plain,(
% 1.32/0.54    ~r1_tarski(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k2_zfmisc_1(sK1,sK3)) | spl5_4),
% 1.32/0.54    inference(resolution,[],[f70,f49])).
% 1.32/0.54  fof(f49,plain,(
% 1.32/0.54    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 1.32/0.54    inference(equality_resolution,[],[f25])).
% 1.32/0.54  fof(f25,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.32/0.54    inference(cnf_transformation,[],[f7])).
% 1.32/0.54  fof(f7,axiom,(
% 1.32/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.32/0.54  fof(f70,plain,(
% 1.32/0.54    ~r2_hidden(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | spl5_4),
% 1.32/0.54    inference(avatar_component_clause,[],[f68])).
% 1.32/0.54  fof(f71,plain,(
% 1.32/0.54    ~spl5_4 | spl5_3),
% 1.32/0.54    inference(avatar_split_clause,[],[f66,f62,f68])).
% 1.32/0.54  fof(f62,plain,(
% 1.32/0.54    spl5_3 <=> m1_subset_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.32/0.54  fof(f66,plain,(
% 1.32/0.54    ~r2_hidden(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | spl5_3),
% 1.32/0.54    inference(resolution,[],[f64,f24])).
% 1.32/0.54  fof(f24,plain,(
% 1.32/0.54    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f16])).
% 1.32/0.54  fof(f16,plain,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.32/0.54    inference(ennf_transformation,[],[f11])).
% 1.32/0.54  fof(f11,axiom,(
% 1.32/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.32/0.54  fof(f64,plain,(
% 1.32/0.54    ~m1_subset_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | spl5_3),
% 1.32/0.54    inference(avatar_component_clause,[],[f62])).
% 1.32/0.54  fof(f65,plain,(
% 1.32/0.54    ~spl5_3),
% 1.32/0.54    inference(avatar_split_clause,[],[f50,f62])).
% 1.32/0.54  fof(f50,plain,(
% 1.32/0.54    ~m1_subset_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 1.32/0.54    inference(forward_demodulation,[],[f43,f47])).
% 1.32/0.54  fof(f47,plain,(
% 1.32/0.54    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X3)) = k5_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 1.32/0.54    inference(definition_unfolding,[],[f34,f41,f41,f39])).
% 1.32/0.54  fof(f34,plain,(
% 1.32/0.54    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f9])).
% 1.32/0.54  fof(f9,axiom,(
% 1.32/0.54    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 1.32/0.54  fof(f43,plain,(
% 1.32/0.54    ~m1_subset_1(k5_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 1.32/0.54    inference(definition_unfolding,[],[f21,f42])).
% 1.32/0.54  fof(f42,plain,(
% 1.32/0.54    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f22,f41])).
% 1.32/0.54  fof(f22,plain,(
% 1.32/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f1])).
% 1.32/0.54  fof(f1,axiom,(
% 1.32/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.54  fof(f21,plain,(
% 1.32/0.54    ~m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 1.32/0.54    inference(cnf_transformation,[],[f15])).
% 1.32/0.54  fof(f15,plain,(
% 1.32/0.54    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r2_hidden(X2,X3) & r2_hidden(X0,X1))),
% 1.32/0.54    inference(flattening,[],[f14])).
% 1.32/0.54  fof(f14,plain,(
% 1.32/0.54    ? [X0,X1,X2,X3] : (~m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & (r2_hidden(X2,X3) & r2_hidden(X0,X1)))),
% 1.32/0.54    inference(ennf_transformation,[],[f13])).
% 1.32/0.54  % (9021)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.54  fof(f13,negated_conjecture,(
% 1.32/0.54    ~! [X0,X1,X2,X3] : ((r2_hidden(X2,X3) & r2_hidden(X0,X1)) => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),
% 1.32/0.54    inference(negated_conjecture,[],[f12])).
% 1.32/0.54  fof(f12,conjecture,(
% 1.32/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(X2,X3) & r2_hidden(X0,X1)) => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_relset_1)).
% 1.32/0.54  fof(f60,plain,(
% 1.32/0.54    spl5_2),
% 1.32/0.54    inference(avatar_split_clause,[],[f20,f57])).
% 1.32/0.54  fof(f20,plain,(
% 1.32/0.54    r2_hidden(sK2,sK3)),
% 1.32/0.54    inference(cnf_transformation,[],[f15])).
% 1.32/0.54  fof(f55,plain,(
% 1.32/0.54    spl5_1),
% 1.32/0.54    inference(avatar_split_clause,[],[f19,f52])).
% 1.32/0.54  fof(f19,plain,(
% 1.32/0.54    r2_hidden(sK0,sK1)),
% 1.32/0.54    inference(cnf_transformation,[],[f15])).
% 1.32/0.54  % SZS output end Proof for theBenchmark
% 1.32/0.54  % (9025)------------------------------
% 1.32/0.54  % (9025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (9025)Termination reason: Refutation
% 1.32/0.54  
% 1.32/0.54  % (9025)Memory used [KB]: 10746
% 1.32/0.54  % (9025)Time elapsed: 0.078 s
% 1.32/0.54  % (9025)------------------------------
% 1.32/0.54  % (9025)------------------------------
% 1.32/0.55  % (9000)Success in time 0.179 s
%------------------------------------------------------------------------------

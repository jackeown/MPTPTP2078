%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:55 EST 2020

% Result     : Theorem 3.31s
% Output     : Refutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 161 expanded)
%              Number of leaves         :   16 (  54 expanded)
%              Depth                    :   19
%              Number of atoms          :  203 ( 447 expanded)
%              Number of equality atoms :   33 (  71 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3904,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f69,f166,f3413,f3630,f3631,f3891])).

fof(f3891,plain,
    ( spl6_2
    | ~ spl6_5
    | ~ spl6_15
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f3860,f3427,f164,f66,f51])).

fof(f51,plain,
    ( spl6_2
  <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f66,plain,
    ( spl6_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f164,plain,
    ( spl6_15
  <=> ! [X5] : r1_tarski(k9_relat_1(sK2,X5),k9_relat_1(sK3,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f3427,plain,
    ( spl6_32
  <=> sK1 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f3860,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))
    | ~ spl6_5
    | ~ spl6_15
    | ~ spl6_32 ),
    inference(superposition,[],[f663,f3429])).

fof(f3429,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f3427])).

fof(f663,plain,
    ( ! [X4,X5] : r1_tarski(k9_relat_1(sK2,X5),k9_relat_1(sK3,k2_xboole_0(X4,X5)))
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(superposition,[],[f177,f179])).

fof(f179,plain,
    ( ! [X2,X3] : k9_relat_1(sK3,k2_xboole_0(X2,X3)) = k2_xboole_0(k9_relat_1(sK3,X2),k9_relat_1(sK3,X3))
    | ~ spl6_5 ),
    inference(resolution,[],[f32,f68])).

fof(f68,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

fof(f177,plain,
    ( ! [X4,X3] : r1_tarski(k9_relat_1(sK2,X3),k2_xboole_0(X4,k9_relat_1(sK3,X3)))
    | ~ spl6_15 ),
    inference(resolution,[],[f165,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f165,plain,
    ( ! [X5] : r1_tarski(k9_relat_1(sK2,X5),k9_relat_1(sK3,X5))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f164])).

fof(f3631,plain,
    ( spl6_32
    | ~ spl6_3
    | spl6_30 ),
    inference(avatar_split_clause,[],[f3414,f3406,f56,f3427])).

fof(f56,plain,
    ( spl6_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f3406,plain,
    ( spl6_30
  <=> r2_hidden(sK5(sK1,sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f3414,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl6_3
    | spl6_30 ),
    inference(resolution,[],[f3408,f2669])).

fof(f2669,plain,
    ( ! [X118] :
        ( r2_hidden(sK5(X118,sK0,X118),sK1)
        | k2_xboole_0(X118,sK0) = X118 )
    | ~ spl6_3 ),
    inference(resolution,[],[f2637,f58])).

fof(f58,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f2637,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,X4)
      | r2_hidden(sK5(X2,X3,X2),X4)
      | k2_xboole_0(X2,X3) = X2 ) ),
    inference(global_subsumption,[],[f2357])).

fof(f2357,plain,(
    ! [X6,X7,X5] :
      ( k2_xboole_0(X5,X6) = X5
      | r2_hidden(sK5(X5,X6,X5),X7)
      | ~ r1_tarski(X6,X7) ) ),
    inference(resolution,[],[f2352,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f2352,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK5(X4,X5,X4),X5)
      | k2_xboole_0(X4,X5) = X4 ) ),
    inference(global_subsumption,[],[f1975])).

fof(f1975,plain,(
    ! [X50,X49] :
      ( k2_xboole_0(X49,X50) = X49
      | r2_hidden(sK5(X49,X50,X49),X50) ) ),
    inference(global_subsumption,[],[f1974])).

fof(f1974,plain,(
    ! [X47,X46] :
      ( k2_xboole_0(X46,X47) = X46
      | r2_hidden(sK5(X46,X47,X46),X47) ) ),
    inference(global_subsumption,[],[f1973])).

fof(f1973,plain,(
    ! [X6,X7] :
      ( k2_xboole_0(X6,X7) = X6
      | r2_hidden(sK5(X6,X7,X6),X7) ) ),
    inference(global_subsumption,[],[f1972])).

fof(f1972,plain,(
    ! [X4,X3] :
      ( k2_xboole_0(X3,X4) = X3
      | r2_hidden(sK5(X3,X4,X3),X4) ) ),
    inference(global_subsumption,[],[f1971])).

fof(f1971,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | r2_hidden(sK5(X0,X1,X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f1910])).

fof(f1910,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | r2_hidden(sK5(X0,X1,X0),X1)
      | r2_hidden(sK5(X0,X1,X0),X1)
      | k2_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f384,f224])).

fof(f224,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,X3,X2),X2)
      | r2_hidden(sK5(X2,X3,X2),X3)
      | k2_xboole_0(X2,X3) = X2 ) ),
    inference(factoring,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f384,plain,(
    ! [X14,X13] :
      ( ~ r2_hidden(sK5(X13,X14,X13),X13)
      | k2_xboole_0(X13,X14) = X13
      | r2_hidden(sK5(X13,X14,X13),X14) ) ),
    inference(duplicate_literal_removal,[],[f374])).

fof(f374,plain,(
    ! [X14,X13] :
      ( r2_hidden(sK5(X13,X14,X13),X14)
      | k2_xboole_0(X13,X14) = X13
      | ~ r2_hidden(sK5(X13,X14,X13),X13)
      | k2_xboole_0(X13,X14) = X13 ) ),
    inference(resolution,[],[f224,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3408,plain,
    ( ~ r2_hidden(sK5(sK1,sK0,sK1),sK1)
    | spl6_30 ),
    inference(avatar_component_clause,[],[f3406])).

fof(f3630,plain,
    ( spl6_2
    | ~ spl6_5
    | ~ spl6_15
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f3561,f3410,f164,f66,f51])).

fof(f3410,plain,
    ( spl6_31
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f3561,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))
    | ~ spl6_5
    | ~ spl6_15
    | ~ spl6_31 ),
    inference(superposition,[],[f962,f3412])).

fof(f3412,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f3410])).

fof(f962,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK3,k2_xboole_0(X0,X1)))
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(superposition,[],[f661,f179])).

fof(f661,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,X1),k2_xboole_0(k9_relat_1(sK3,X1),X0))
    | ~ spl6_15 ),
    inference(superposition,[],[f177,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f3413,plain,
    ( ~ spl6_30
    | spl6_31
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f3404,f56,f3410,f3406])).

fof(f3404,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ r2_hidden(sK5(sK1,sK0,sK1),sK1)
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f3403,f24])).

fof(f3403,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ r2_hidden(sK5(sK1,sK0,sK1),sK1)
    | ~ spl6_3 ),
    inference(duplicate_literal_removal,[],[f3397])).

fof(f3397,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ r2_hidden(sK5(sK1,sK0,sK1),sK1)
    | sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f2669,f34])).

fof(f166,plain,
    ( spl6_15
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f135,f61,f66,f46,f164])).

fof(f46,plain,
    ( spl6_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f61,plain,
    ( spl6_4
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f135,plain,
    ( ! [X5] :
        ( ~ v1_relat_1(sK3)
        | ~ v1_relat_1(sK2)
        | r1_tarski(k9_relat_1(sK2,X5),k9_relat_1(sK3,X5)) )
    | ~ spl6_4 ),
    inference(resolution,[],[f25,f63])).

fof(f63,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

fof(f69,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f18,f66])).

fof(f18,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(f64,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f19,f61])).

fof(f19,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f20,f56])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f54,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f49,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f22,f46])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:23:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (29519)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (29540)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (29537)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.50  % (29545)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (29547)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (29540)Refutation not found, incomplete strategy% (29540)------------------------------
% 0.21/0.51  % (29540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29540)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29540)Memory used [KB]: 10746
% 0.21/0.51  % (29540)Time elapsed: 0.079 s
% 0.21/0.51  % (29540)------------------------------
% 0.21/0.51  % (29540)------------------------------
% 0.21/0.51  % (29536)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (29539)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (29525)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (29526)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (29520)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (29523)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (29522)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (29538)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (29524)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (29535)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (29529)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (29518)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (29529)Refutation not found, incomplete strategy% (29529)------------------------------
% 0.21/0.53  % (29529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29516)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (29517)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (29546)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (29529)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29529)Memory used [KB]: 10618
% 0.21/0.54  % (29529)Time elapsed: 0.121 s
% 0.21/0.54  % (29529)------------------------------
% 0.21/0.54  % (29529)------------------------------
% 0.21/0.54  % (29543)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (29544)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (29528)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (29531)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (29541)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (29542)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (29530)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (29535)Refutation not found, incomplete strategy% (29535)------------------------------
% 0.21/0.54  % (29535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29535)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29535)Memory used [KB]: 10618
% 0.21/0.54  % (29535)Time elapsed: 0.140 s
% 0.21/0.54  % (29535)------------------------------
% 0.21/0.54  % (29535)------------------------------
% 0.21/0.55  % (29532)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (29533)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (29534)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.06/0.65  % (29578)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.06/0.67  % (29580)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.06/0.67  % (29579)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.31/0.83  % (29534)Refutation found. Thanks to Tanya!
% 3.31/0.83  % SZS status Theorem for theBenchmark
% 3.31/0.83  % SZS output start Proof for theBenchmark
% 3.31/0.83  fof(f3904,plain,(
% 3.31/0.83    $false),
% 3.31/0.83    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f69,f166,f3413,f3630,f3631,f3891])).
% 3.31/0.83  fof(f3891,plain,(
% 3.31/0.83    spl6_2 | ~spl6_5 | ~spl6_15 | ~spl6_32),
% 3.31/0.83    inference(avatar_split_clause,[],[f3860,f3427,f164,f66,f51])).
% 3.31/0.83  fof(f51,plain,(
% 3.31/0.83    spl6_2 <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),
% 3.31/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 3.31/0.83  fof(f66,plain,(
% 3.31/0.83    spl6_5 <=> v1_relat_1(sK3)),
% 3.31/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 3.31/0.83  fof(f164,plain,(
% 3.31/0.83    spl6_15 <=> ! [X5] : r1_tarski(k9_relat_1(sK2,X5),k9_relat_1(sK3,X5))),
% 3.31/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 3.31/0.83  fof(f3427,plain,(
% 3.31/0.83    spl6_32 <=> sK1 = k2_xboole_0(sK1,sK0)),
% 3.31/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 3.31/0.83  fof(f3860,plain,(
% 3.31/0.83    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) | (~spl6_5 | ~spl6_15 | ~spl6_32)),
% 3.31/0.83    inference(superposition,[],[f663,f3429])).
% 3.31/0.83  fof(f3429,plain,(
% 3.31/0.83    sK1 = k2_xboole_0(sK1,sK0) | ~spl6_32),
% 3.31/0.83    inference(avatar_component_clause,[],[f3427])).
% 3.31/0.83  fof(f663,plain,(
% 3.31/0.83    ( ! [X4,X5] : (r1_tarski(k9_relat_1(sK2,X5),k9_relat_1(sK3,k2_xboole_0(X4,X5)))) ) | (~spl6_5 | ~spl6_15)),
% 3.31/0.83    inference(superposition,[],[f177,f179])).
% 3.31/0.83  fof(f179,plain,(
% 3.31/0.83    ( ! [X2,X3] : (k9_relat_1(sK3,k2_xboole_0(X2,X3)) = k2_xboole_0(k9_relat_1(sK3,X2),k9_relat_1(sK3,X3))) ) | ~spl6_5),
% 3.31/0.83    inference(resolution,[],[f32,f68])).
% 3.31/0.83  fof(f68,plain,(
% 3.31/0.83    v1_relat_1(sK3) | ~spl6_5),
% 3.31/0.83    inference(avatar_component_clause,[],[f66])).
% 3.31/0.83  fof(f32,plain,(
% 3.31/0.83    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 3.31/0.83    inference(cnf_transformation,[],[f16])).
% 3.31/0.83  fof(f16,plain,(
% 3.31/0.83    ! [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 3.31/0.83    inference(ennf_transformation,[],[f7])).
% 3.31/0.83  fof(f7,axiom,(
% 3.31/0.83    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 3.31/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).
% 3.31/0.83  fof(f177,plain,(
% 3.31/0.83    ( ! [X4,X3] : (r1_tarski(k9_relat_1(sK2,X3),k2_xboole_0(X4,k9_relat_1(sK3,X3)))) ) | ~spl6_15),
% 3.31/0.83    inference(resolution,[],[f165,f33])).
% 3.31/0.83  fof(f33,plain,(
% 3.31/0.83    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 3.31/0.83    inference(cnf_transformation,[],[f17])).
% 3.31/0.83  fof(f17,plain,(
% 3.31/0.83    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.31/0.83    inference(ennf_transformation,[],[f5])).
% 3.31/0.83  fof(f5,axiom,(
% 3.31/0.83    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.31/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 3.31/0.83  fof(f165,plain,(
% 3.31/0.83    ( ! [X5] : (r1_tarski(k9_relat_1(sK2,X5),k9_relat_1(sK3,X5))) ) | ~spl6_15),
% 3.31/0.83    inference(avatar_component_clause,[],[f164])).
% 3.31/0.83  fof(f3631,plain,(
% 3.31/0.83    spl6_32 | ~spl6_3 | spl6_30),
% 3.31/0.83    inference(avatar_split_clause,[],[f3414,f3406,f56,f3427])).
% 3.31/0.83  fof(f56,plain,(
% 3.31/0.83    spl6_3 <=> r1_tarski(sK0,sK1)),
% 3.31/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 3.31/0.83  fof(f3406,plain,(
% 3.31/0.83    spl6_30 <=> r2_hidden(sK5(sK1,sK0,sK1),sK1)),
% 3.31/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 3.31/0.83  fof(f3414,plain,(
% 3.31/0.83    sK1 = k2_xboole_0(sK1,sK0) | (~spl6_3 | spl6_30)),
% 3.31/0.83    inference(resolution,[],[f3408,f2669])).
% 3.31/0.83  fof(f2669,plain,(
% 3.31/0.83    ( ! [X118] : (r2_hidden(sK5(X118,sK0,X118),sK1) | k2_xboole_0(X118,sK0) = X118) ) | ~spl6_3),
% 3.31/0.83    inference(resolution,[],[f2637,f58])).
% 3.31/0.83  fof(f58,plain,(
% 3.31/0.83    r1_tarski(sK0,sK1) | ~spl6_3),
% 3.31/0.83    inference(avatar_component_clause,[],[f56])).
% 3.31/0.83  fof(f2637,plain,(
% 3.31/0.83    ( ! [X4,X2,X3] : (~r1_tarski(X3,X4) | r2_hidden(sK5(X2,X3,X2),X4) | k2_xboole_0(X2,X3) = X2) )),
% 3.31/0.83    inference(global_subsumption,[],[f2357])).
% 3.31/0.83  fof(f2357,plain,(
% 3.31/0.83    ( ! [X6,X7,X5] : (k2_xboole_0(X5,X6) = X5 | r2_hidden(sK5(X5,X6,X5),X7) | ~r1_tarski(X6,X7)) )),
% 3.31/0.83    inference(resolution,[],[f2352,f29])).
% 3.31/0.83  fof(f29,plain,(
% 3.31/0.83    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.31/0.83    inference(cnf_transformation,[],[f15])).
% 3.31/0.83  fof(f15,plain,(
% 3.31/0.83    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.31/0.83    inference(ennf_transformation,[],[f2])).
% 3.31/0.83  fof(f2,axiom,(
% 3.31/0.83    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.31/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.31/0.83  fof(f2352,plain,(
% 3.31/0.83    ( ! [X4,X5] : (r2_hidden(sK5(X4,X5,X4),X5) | k2_xboole_0(X4,X5) = X4) )),
% 3.31/0.83    inference(global_subsumption,[],[f1975])).
% 3.31/0.83  fof(f1975,plain,(
% 3.31/0.83    ( ! [X50,X49] : (k2_xboole_0(X49,X50) = X49 | r2_hidden(sK5(X49,X50,X49),X50)) )),
% 3.31/0.83    inference(global_subsumption,[],[f1974])).
% 3.31/0.83  fof(f1974,plain,(
% 3.31/0.83    ( ! [X47,X46] : (k2_xboole_0(X46,X47) = X46 | r2_hidden(sK5(X46,X47,X46),X47)) )),
% 3.31/0.83    inference(global_subsumption,[],[f1973])).
% 3.31/0.83  fof(f1973,plain,(
% 3.31/0.83    ( ! [X6,X7] : (k2_xboole_0(X6,X7) = X6 | r2_hidden(sK5(X6,X7,X6),X7)) )),
% 3.31/0.83    inference(global_subsumption,[],[f1972])).
% 3.31/0.83  fof(f1972,plain,(
% 3.31/0.83    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = X3 | r2_hidden(sK5(X3,X4,X3),X4)) )),
% 3.31/0.83    inference(global_subsumption,[],[f1971])).
% 3.31/0.83  fof(f1971,plain,(
% 3.31/0.83    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | r2_hidden(sK5(X0,X1,X0),X1)) )),
% 3.31/0.83    inference(duplicate_literal_removal,[],[f1910])).
% 3.31/0.83  fof(f1910,plain,(
% 3.31/0.83    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | r2_hidden(sK5(X0,X1,X0),X1) | r2_hidden(sK5(X0,X1,X0),X1) | k2_xboole_0(X0,X1) = X0) )),
% 3.31/0.83    inference(resolution,[],[f384,f224])).
% 3.31/0.83  fof(f224,plain,(
% 3.31/0.83    ( ! [X2,X3] : (r2_hidden(sK5(X2,X3,X2),X2) | r2_hidden(sK5(X2,X3,X2),X3) | k2_xboole_0(X2,X3) = X2) )),
% 3.31/0.83    inference(factoring,[],[f36])).
% 3.31/0.83  fof(f36,plain,(
% 3.31/0.83    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 3.31/0.83    inference(cnf_transformation,[],[f3])).
% 3.31/0.83  fof(f3,axiom,(
% 3.31/0.83    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.31/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 3.31/0.83  fof(f384,plain,(
% 3.31/0.83    ( ! [X14,X13] : (~r2_hidden(sK5(X13,X14,X13),X13) | k2_xboole_0(X13,X14) = X13 | r2_hidden(sK5(X13,X14,X13),X14)) )),
% 3.31/0.83    inference(duplicate_literal_removal,[],[f374])).
% 3.31/0.83  fof(f374,plain,(
% 3.31/0.83    ( ! [X14,X13] : (r2_hidden(sK5(X13,X14,X13),X14) | k2_xboole_0(X13,X14) = X13 | ~r2_hidden(sK5(X13,X14,X13),X13) | k2_xboole_0(X13,X14) = X13) )),
% 3.31/0.83    inference(resolution,[],[f224,f34])).
% 3.31/0.83  fof(f34,plain,(
% 3.31/0.83    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 3.31/0.83    inference(cnf_transformation,[],[f3])).
% 3.31/0.83  fof(f3408,plain,(
% 3.31/0.83    ~r2_hidden(sK5(sK1,sK0,sK1),sK1) | spl6_30),
% 3.31/0.83    inference(avatar_component_clause,[],[f3406])).
% 3.31/0.83  fof(f3630,plain,(
% 3.31/0.83    spl6_2 | ~spl6_5 | ~spl6_15 | ~spl6_31),
% 3.31/0.83    inference(avatar_split_clause,[],[f3561,f3410,f164,f66,f51])).
% 3.31/0.83  fof(f3410,plain,(
% 3.31/0.83    spl6_31 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 3.31/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 3.31/0.83  fof(f3561,plain,(
% 3.31/0.83    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) | (~spl6_5 | ~spl6_15 | ~spl6_31)),
% 3.31/0.83    inference(superposition,[],[f962,f3412])).
% 3.31/0.83  fof(f3412,plain,(
% 3.31/0.83    sK1 = k2_xboole_0(sK0,sK1) | ~spl6_31),
% 3.31/0.83    inference(avatar_component_clause,[],[f3410])).
% 3.31/0.83  fof(f962,plain,(
% 3.31/0.83    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK3,k2_xboole_0(X0,X1)))) ) | (~spl6_5 | ~spl6_15)),
% 3.31/0.83    inference(superposition,[],[f661,f179])).
% 3.31/0.83  fof(f661,plain,(
% 3.31/0.83    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X1),k2_xboole_0(k9_relat_1(sK3,X1),X0))) ) | ~spl6_15),
% 3.31/0.83    inference(superposition,[],[f177,f24])).
% 3.31/0.83  fof(f24,plain,(
% 3.31/0.83    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.31/0.83    inference(cnf_transformation,[],[f1])).
% 3.31/0.83  fof(f1,axiom,(
% 3.31/0.83    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.31/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.31/0.83  fof(f3413,plain,(
% 3.31/0.83    ~spl6_30 | spl6_31 | ~spl6_3),
% 3.31/0.83    inference(avatar_split_clause,[],[f3404,f56,f3410,f3406])).
% 3.31/0.83  fof(f3404,plain,(
% 3.31/0.83    sK1 = k2_xboole_0(sK0,sK1) | ~r2_hidden(sK5(sK1,sK0,sK1),sK1) | ~spl6_3),
% 3.31/0.83    inference(forward_demodulation,[],[f3403,f24])).
% 3.31/0.83  fof(f3403,plain,(
% 3.31/0.83    sK1 = k2_xboole_0(sK1,sK0) | ~r2_hidden(sK5(sK1,sK0,sK1),sK1) | ~spl6_3),
% 3.31/0.83    inference(duplicate_literal_removal,[],[f3397])).
% 3.31/0.83  fof(f3397,plain,(
% 3.31/0.83    sK1 = k2_xboole_0(sK1,sK0) | ~r2_hidden(sK5(sK1,sK0,sK1),sK1) | sK1 = k2_xboole_0(sK1,sK0) | ~spl6_3),
% 3.31/0.83    inference(resolution,[],[f2669,f34])).
% 3.31/0.83  fof(f166,plain,(
% 3.31/0.83    spl6_15 | ~spl6_1 | ~spl6_5 | ~spl6_4),
% 3.31/0.83    inference(avatar_split_clause,[],[f135,f61,f66,f46,f164])).
% 3.31/0.83  fof(f46,plain,(
% 3.31/0.83    spl6_1 <=> v1_relat_1(sK2)),
% 3.31/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 3.31/0.83  fof(f61,plain,(
% 3.31/0.83    spl6_4 <=> r1_tarski(sK2,sK3)),
% 3.31/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 3.31/0.83  fof(f135,plain,(
% 3.31/0.83    ( ! [X5] : (~v1_relat_1(sK3) | ~v1_relat_1(sK2) | r1_tarski(k9_relat_1(sK2,X5),k9_relat_1(sK3,X5))) ) | ~spl6_4),
% 3.31/0.83    inference(resolution,[],[f25,f63])).
% 3.31/0.83  fof(f63,plain,(
% 3.31/0.83    r1_tarski(sK2,sK3) | ~spl6_4),
% 3.31/0.83    inference(avatar_component_clause,[],[f61])).
% 3.31/0.83  fof(f25,plain,(
% 3.31/0.83    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))) )),
% 3.31/0.83    inference(cnf_transformation,[],[f14])).
% 3.31/0.83  fof(f14,plain,(
% 3.31/0.83    ! [X0,X1] : (! [X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.31/0.83    inference(flattening,[],[f13])).
% 3.31/0.83  fof(f13,plain,(
% 3.31/0.83    ! [X0,X1] : (! [X2] : ((r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.31/0.83    inference(ennf_transformation,[],[f8])).
% 3.31/0.83  fof(f8,axiom,(
% 3.31/0.83    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 3.31/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).
% 3.31/0.83  fof(f69,plain,(
% 3.31/0.83    spl6_5),
% 3.31/0.83    inference(avatar_split_clause,[],[f18,f66])).
% 3.31/0.83  fof(f18,plain,(
% 3.31/0.83    v1_relat_1(sK3)),
% 3.31/0.83    inference(cnf_transformation,[],[f12])).
% 3.31/0.83  fof(f12,plain,(
% 3.31/0.83    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 3.31/0.83    inference(flattening,[],[f11])).
% 3.31/0.83  fof(f11,plain,(
% 3.31/0.83    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 3.31/0.83    inference(ennf_transformation,[],[f10])).
% 3.31/0.83  fof(f10,negated_conjecture,(
% 3.31/0.83    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 3.31/0.83    inference(negated_conjecture,[],[f9])).
% 3.31/0.83  fof(f9,conjecture,(
% 3.31/0.83    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 3.31/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).
% 3.31/0.83  fof(f64,plain,(
% 3.31/0.83    spl6_4),
% 3.31/0.83    inference(avatar_split_clause,[],[f19,f61])).
% 3.31/0.83  fof(f19,plain,(
% 3.31/0.83    r1_tarski(sK2,sK3)),
% 3.31/0.83    inference(cnf_transformation,[],[f12])).
% 3.31/0.83  fof(f59,plain,(
% 3.31/0.83    spl6_3),
% 3.31/0.83    inference(avatar_split_clause,[],[f20,f56])).
% 3.31/0.83  fof(f20,plain,(
% 3.31/0.83    r1_tarski(sK0,sK1)),
% 3.31/0.83    inference(cnf_transformation,[],[f12])).
% 3.31/0.83  fof(f54,plain,(
% 3.31/0.83    ~spl6_2),
% 3.31/0.83    inference(avatar_split_clause,[],[f21,f51])).
% 3.31/0.83  fof(f21,plain,(
% 3.31/0.83    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),
% 3.31/0.83    inference(cnf_transformation,[],[f12])).
% 3.31/0.83  fof(f49,plain,(
% 3.31/0.83    spl6_1),
% 3.31/0.83    inference(avatar_split_clause,[],[f22,f46])).
% 3.31/0.83  fof(f22,plain,(
% 3.31/0.83    v1_relat_1(sK2)),
% 3.31/0.83    inference(cnf_transformation,[],[f12])).
% 3.31/0.83  % SZS output end Proof for theBenchmark
% 3.31/0.83  % (29534)------------------------------
% 3.31/0.83  % (29534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.31/0.83  % (29534)Termination reason: Refutation
% 3.31/0.83  
% 3.31/0.83  % (29534)Memory used [KB]: 13816
% 3.31/0.83  % (29534)Time elapsed: 0.434 s
% 3.31/0.83  % (29534)------------------------------
% 3.31/0.83  % (29534)------------------------------
% 3.31/0.83  % (29522)Time limit reached!
% 3.31/0.83  % (29522)------------------------------
% 3.31/0.83  % (29522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.31/0.83  % (29522)Termination reason: Time limit
% 3.31/0.83  % (29522)Termination phase: Saturation
% 3.31/0.83  
% 3.31/0.83  % (29522)Memory used [KB]: 8571
% 3.31/0.83  % (29522)Time elapsed: 0.400 s
% 3.31/0.83  % (29522)------------------------------
% 3.31/0.83  % (29522)------------------------------
% 3.31/0.84  % (29511)Success in time 0.476 s
%------------------------------------------------------------------------------

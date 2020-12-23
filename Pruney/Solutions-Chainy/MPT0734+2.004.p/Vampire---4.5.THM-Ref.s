%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 (  79 expanded)
%              Number of leaves         :   10 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  126 ( 276 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f139,f168])).

fof(f168,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | ~ spl4_7 ),
    inference(resolution,[],[f150,f40])).

fof(f40,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f150,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f57,f125])).

fof(f125,plain,
    ( sK1 = sK2
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_7
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f57,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f21,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f21,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ! [X2] :
                ( v3_ordinal1(X2)
               => ( ( r2_hidden(X1,X2)
                    & r1_tarski(X0,X1) )
                 => r2_hidden(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r2_hidden(X1,X2)
                  & r1_tarski(X0,X1) )
               => r2_hidden(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_ordinal1)).

fof(f139,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f61,f127])).

fof(f127,plain,
    ( r2_xboole_0(sK0,sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f121,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_xboole_0(sK1,X0)
      | r2_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f20,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X2)
      | r2_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l58_xboole_1)).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f121,plain,
    ( r2_xboole_0(sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_6
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f61,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(global_subsumption,[],[f19,f24,f60])).

fof(f60,plain,
    ( ~ v1_ordinal1(sK0)
    | ~ v3_ordinal1(sK2)
    | ~ r2_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f22,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ r2_xboole_0(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f22,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    v1_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f126,plain,
    ( spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f69,f123,f119])).

fof(f69,plain,
    ( sK1 = sK2
    | r2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f59,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

% (4434)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f59,plain,(
    r1_tarski(sK1,sK2) ),
    inference(global_subsumption,[],[f42,f58])).

fof(f58,plain,
    ( r1_tarski(sK1,sK2)
    | ~ v1_ordinal1(sK2) ),
    inference(resolution,[],[f21,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_tarski(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f42,plain,(
    v1_ordinal1(sK2) ),
    inference(resolution,[],[f19,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:38:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (4435)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.49  % (4435)Refutation not found, incomplete strategy% (4435)------------------------------
% 0.22/0.49  % (4435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (4435)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (4435)Memory used [KB]: 6140
% 0.22/0.49  % (4435)Time elapsed: 0.075 s
% 0.22/0.49  % (4435)------------------------------
% 0.22/0.49  % (4435)------------------------------
% 0.22/0.49  % (4450)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.50  % (4450)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f126,f139,f168])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    ~spl4_7),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f165])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    $false | ~spl4_7),
% 0.22/0.50    inference(resolution,[],[f150,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    ~r1_tarski(sK1,sK1) | ~spl4_7),
% 0.22/0.50    inference(backward_demodulation,[],[f57,f125])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    sK1 = sK2 | ~spl4_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f123])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    spl4_7 <=> sK1 = sK2),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ~r1_tarski(sK2,sK1)),
% 0.22/0.50    inference(resolution,[],[f21,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    r2_hidden(sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X0,X2) & r2_hidden(X1,X2) & r1_tarski(X0,X1) & v3_ordinal1(X2)) & v3_ordinal1(X1)) & v1_ordinal1(X0))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X0,X2) & (r2_hidden(X1,X2) & r1_tarski(X0,X1))) & v3_ordinal1(X2)) & v3_ordinal1(X1)) & v1_ordinal1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ! [X2] : (v3_ordinal1(X2) => ((r2_hidden(X1,X2) & r1_tarski(X0,X1)) => r2_hidden(X0,X2)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f8])).
% 0.22/0.50  fof(f8,conjecture,(
% 0.22/0.50    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ! [X2] : (v3_ordinal1(X2) => ((r2_hidden(X1,X2) & r1_tarski(X0,X1)) => r2_hidden(X0,X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_ordinal1)).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    ~spl4_6),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f134])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    $false | ~spl4_6),
% 0.22/0.50    inference(subsumption_resolution,[],[f61,f127])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    r2_xboole_0(sK0,sK2) | ~spl4_6),
% 0.22/0.50    inference(resolution,[],[f121,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_xboole_0(sK1,X0) | r2_xboole_0(sK0,X0)) )),
% 0.22/0.50    inference(resolution,[],[f20,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X2) | r2_xboole_0(X0,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | ~r2_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | (~r2_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l58_xboole_1)).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    r1_tarski(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    r2_xboole_0(sK1,sK2) | ~spl4_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f119])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    spl4_6 <=> r2_xboole_0(sK1,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ~r2_xboole_0(sK0,sK2)),
% 0.22/0.50    inference(global_subsumption,[],[f19,f24,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ~v1_ordinal1(sK0) | ~v3_ordinal1(sK2) | ~r2_xboole_0(sK0,sK2)),
% 0.22/0.50    inference(resolution,[],[f22,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_ordinal1(X0) | ~v3_ordinal1(X1) | ~r2_xboole_0(X0,X1) | r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ~r2_hidden(sK0,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    v1_ordinal1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    v3_ordinal1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    spl4_6 | spl4_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f69,f123,f119])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    sK1 = sK2 | r2_xboole_0(sK1,sK2)),
% 0.22/0.50    inference(resolution,[],[f59,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  % (4434)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    r1_tarski(sK1,sK2)),
% 0.22/0.50    inference(global_subsumption,[],[f42,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    r1_tarski(sK1,sK2) | ~v1_ordinal1(sK2)),
% 0.22/0.50    inference(resolution,[],[f21,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r1_tarski(X1,X0) | ~v1_ordinal1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    v1_ordinal1(sK2)),
% 0.22/0.50    inference(resolution,[],[f19,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (4450)------------------------------
% 0.22/0.50  % (4450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (4450)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (4450)Memory used [KB]: 10618
% 0.22/0.50  % (4450)Time elapsed: 0.079 s
% 0.22/0.50  % (4450)------------------------------
% 0.22/0.50  % (4450)------------------------------
% 0.22/0.50  % (4433)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (4426)Success in time 0.14 s
%------------------------------------------------------------------------------

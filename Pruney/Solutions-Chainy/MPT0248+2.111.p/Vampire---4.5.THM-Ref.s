%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 113 expanded)
%              Number of leaves         :   17 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :  152 ( 293 expanded)
%              Number of equality atoms :   62 ( 160 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f43,f48,f53,f59,f80,f87,f137,f138,f152,f157,f171])).

fof(f171,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f170,f149,f45,f154])).

fof(f154,plain,
    ( spl3_13
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f45,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f149,plain,
    ( spl3_12
  <=> k1_tarski(sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f170,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f169,f60])).

fof(f60,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f18,f16])).

fof(f16,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f169,plain,
    ( k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f151,f46])).

fof(f46,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f151,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f149])).

fof(f157,plain,
    ( ~ spl3_13
    | spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f140,f50,f36,f154])).

fof(f36,plain,
    ( spl3_2
  <=> sK2 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f50,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f140,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | spl3_2
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f38,f51])).

fof(f51,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f38,plain,
    ( sK2 != k1_tarski(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f152,plain,
    ( spl3_12
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f139,f50,f31,f149])).

fof(f31,plain,
    ( spl3_1
  <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f139,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f33,f51])).

fof(f33,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f138,plain,
    ( spl3_5
    | spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f134,f84,f36,f50])).

fof(f84,plain,
    ( spl3_9
  <=> r1_tarski(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f134,plain,
    ( sK2 = k1_tarski(sK0)
    | k1_xboole_0 = sK2
    | ~ spl3_9 ),
    inference(resolution,[],[f22,f86])).

fof(f86,plain,
    ( r1_tarski(sK2,k1_tarski(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f137,plain,
    ( spl3_4
    | spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f132,f56,f40,f45])).

fof(f40,plain,
    ( spl3_3
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f56,plain,
    ( spl3_6
  <=> r1_tarski(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f132,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1
    | ~ spl3_6 ),
    inference(resolution,[],[f22,f58])).

fof(f58,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f87,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f82,f77,f84])).

fof(f77,plain,
    ( spl3_8
  <=> k1_tarski(sK0) = k2_xboole_0(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f82,plain,
    ( r1_tarski(sK2,k1_tarski(sK0))
    | ~ spl3_8 ),
    inference(superposition,[],[f17,f79])).

fof(f79,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK2,k1_tarski(sK0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f80,plain,
    ( spl3_8
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f75,f31,f77])).

fof(f75,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK2,k1_tarski(sK0))
    | ~ spl3_1 ),
    inference(resolution,[],[f71,f26])).

fof(f26,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f71,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | k1_tarski(sK0) = k2_xboole_0(X0,k1_tarski(sK0)) )
    | ~ spl3_1 ),
    inference(resolution,[],[f70,f18])).

fof(f70,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_tarski(sK0))
        | ~ r1_tarski(X0,sK2) )
    | ~ spl3_1 ),
    inference(superposition,[],[f25,f33])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f59,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f54,f31,f56])).

fof(f54,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl3_1 ),
    inference(superposition,[],[f17,f33])).

fof(f53,plain,
    ( ~ spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f12,f40,f50])).

fof(f12,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f48,plain,
    ( ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f13,f45,f36])).

fof(f13,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f14,f40,f36])).

fof(f14,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:12:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (26767)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (26779)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (26771)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (26779)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f34,f43,f48,f53,f59,f80,f87,f137,f138,f152,f157,f171])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    spl3_13 | ~spl3_4 | ~spl3_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f170,f149,f45,f154])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    spl3_13 <=> k1_xboole_0 = k1_tarski(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    spl3_4 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    spl3_12 <=> k1_tarski(sK0) = k2_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    k1_xboole_0 = k1_tarski(sK0) | (~spl3_4 | ~spl3_12)),
% 0.21/0.53    inference(forward_demodulation,[],[f169,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.53    inference(resolution,[],[f18,f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl3_4 | ~spl3_12)),
% 0.21/0.53    inference(forward_demodulation,[],[f151,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~spl3_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f45])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,k1_xboole_0) | ~spl3_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f149])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    ~spl3_13 | spl3_2 | ~spl3_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f140,f50,f36,f154])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    spl3_2 <=> sK2 = k1_tarski(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    spl3_5 <=> k1_xboole_0 = sK2),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    k1_xboole_0 != k1_tarski(sK0) | (spl3_2 | ~spl3_5)),
% 0.21/0.53    inference(backward_demodulation,[],[f38,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | ~spl3_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f50])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    sK2 != k1_tarski(sK0) | spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f36])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    spl3_12 | ~spl3_1 | ~spl3_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f139,f50,f31,f149])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    spl3_1 <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,k1_xboole_0) | (~spl3_1 | ~spl3_5)),
% 0.21/0.53    inference(backward_demodulation,[],[f33,f51])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) | ~spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f31])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    spl3_5 | spl3_2 | ~spl3_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f134,f84,f36,f50])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    spl3_9 <=> r1_tarski(sK2,k1_tarski(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    sK2 = k1_tarski(sK0) | k1_xboole_0 = sK2 | ~spl3_9),
% 0.21/0.53    inference(resolution,[],[f22,f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    r1_tarski(sK2,k1_tarski(sK0)) | ~spl3_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f84])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    spl3_4 | spl3_3 | ~spl3_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f132,f56,f40,f45])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    spl3_3 <=> sK1 = k1_tarski(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    spl3_6 <=> r1_tarski(sK1,k1_tarski(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1 | ~spl3_6),
% 0.21/0.53    inference(resolution,[],[f22,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    r1_tarski(sK1,k1_tarski(sK0)) | ~spl3_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f56])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    spl3_9 | ~spl3_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f82,f77,f84])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    spl3_8 <=> k1_tarski(sK0) = k2_xboole_0(sK2,k1_tarski(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    r1_tarski(sK2,k1_tarski(sK0)) | ~spl3_8),
% 0.21/0.53    inference(superposition,[],[f17,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    k1_tarski(sK0) = k2_xboole_0(sK2,k1_tarski(sK0)) | ~spl3_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f77])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    spl3_8 | ~spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f75,f31,f77])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    k1_tarski(sK0) = k2_xboole_0(sK2,k1_tarski(sK0)) | ~spl3_1),
% 0.21/0.53    inference(resolution,[],[f71,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,sK2) | k1_tarski(sK0) = k2_xboole_0(X0,k1_tarski(sK0))) ) | ~spl3_1),
% 0.21/0.53    inference(resolution,[],[f70,f18])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(X0,k1_tarski(sK0)) | ~r1_tarski(X0,sK2)) ) | ~spl3_1),
% 0.21/0.53    inference(superposition,[],[f25,f33])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    spl3_6 | ~spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f54,f31,f56])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    r1_tarski(sK1,k1_tarski(sK0)) | ~spl3_1),
% 0.21/0.53    inference(superposition,[],[f17,f33])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ~spl3_5 | ~spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f12,f40,f50])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.53    inference(negated_conjecture,[],[f7])).
% 0.21/0.53  fof(f7,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ~spl3_2 | ~spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f13,f45,f36])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ~spl3_2 | ~spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f14,f40,f36])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f15,f31])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (26779)------------------------------
% 0.21/0.53  % (26779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26779)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (26779)Memory used [KB]: 6140
% 0.21/0.53  % (26779)Time elapsed: 0.053 s
% 0.21/0.53  % (26779)------------------------------
% 0.21/0.53  % (26779)------------------------------
% 0.21/0.53  % (26763)Success in time 0.172 s
%------------------------------------------------------------------------------

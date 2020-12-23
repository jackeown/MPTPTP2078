%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 145 expanded)
%              Number of leaves         :    9 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :  218 ( 682 expanded)
%              Number of equality atoms :  133 ( 531 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f64,f84,f112,f131,f164,f181])).

fof(f181,plain,
    ( spl3_5
    | spl3_4
    | spl3_3
    | spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f176,f41,f45,f50,f55,f60])).

fof(f60,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f55,plain,
    ( spl3_4
  <=> sK0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f50,plain,
    ( spl3_3
  <=> sK0 = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f45,plain,
    ( spl3_2
  <=> sK0 = k2_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f41,plain,
    ( spl3_1
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f176,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | ~ spl3_1 ),
    inference(resolution,[],[f173,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f173,plain,
    ( r1_tarski(sK0,k2_tarski(sK1,sK2))
    | ~ spl3_1 ),
    inference(trivial_inequality_removal,[],[f172])).

fof(f172,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k2_tarski(sK1,sK2))
    | ~ spl3_1 ),
    inference(superposition,[],[f32,f42])).

fof(f42,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f164,plain,
    ( spl3_1
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl3_1
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f43,f139,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f139,plain,
    ( ! [X5] : r1_tarski(sK0,k2_tarski(sK1,X5))
    | ~ spl3_4 ),
    inference(superposition,[],[f38,f56])).

fof(f56,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f38,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f131,plain,
    ( spl3_1
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl3_1
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f39,f114,f33])).

fof(f114,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK1,sK2))
    | spl3_1
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f43,f61])).

fof(f61,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f39,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f26])).

% (20544)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f112,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f43,f91,f33])).

fof(f91,plain,
    ( ! [X6] : r1_tarski(sK0,k2_tarski(X6,sK2))
    | ~ spl3_3 ),
    inference(superposition,[],[f37,f51])).

fof(f51,plain,
    ( sK0 = k1_tarski(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f37,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f84,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f69,f76,f33])).

fof(f76,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f43,f46])).

fof(f46,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f69,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl3_2 ),
    inference(superposition,[],[f36,f46])).

fof(f36,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,
    ( spl3_1
    | spl3_5
    | spl3_4
    | spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f20,f45,f50,f55,f60,f41])).

fof(f20,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ( sK0 != k2_tarski(sK1,sK2)
        & sK0 != k1_tarski(sK2)
        & sK0 != k1_tarski(sK1)
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
    & ( sK0 = k2_tarski(sK1,sK2)
      | sK0 = k1_tarski(sK2)
      | sK0 = k1_tarski(sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
        & ( k2_tarski(X1,X2) = X0
          | k1_tarski(X2) = X0
          | k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) )
   => ( ( ( sK0 != k2_tarski(sK1,sK2)
          & sK0 != k1_tarski(sK2)
          & sK0 != k1_tarski(sK1)
          & k1_xboole_0 != sK0 )
        | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
      & ( sK0 = k2_tarski(sK1,sK2)
        | sK0 = k1_tarski(sK2)
        | sK0 = k1_tarski(sK1)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f63,plain,
    ( ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f21,f60,f41])).

fof(f21,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,
    ( ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f22,f55,f41])).

fof(f22,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,
    ( ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f23,f50,f41])).

fof(f23,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f24,f45,f41])).

fof(f24,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:24:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.43  % (20551)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.43  % (20551)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f182,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f64,f84,f112,f131,f164,f181])).
% 0.21/0.43  fof(f181,plain,(
% 0.21/0.43    spl3_5 | spl3_4 | spl3_3 | spl3_2 | ~spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f176,f41,f45,f50,f55,f60])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    spl3_5 <=> k1_xboole_0 = sK0),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl3_4 <=> sK0 = k1_tarski(sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    spl3_3 <=> sK0 = k1_tarski(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    spl3_2 <=> sK0 = k2_tarski(sK1,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    spl3_1 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.43  fof(f176,plain,(
% 0.21/0.43    sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | ~spl3_1),
% 0.21/0.43    inference(resolution,[],[f173,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.43    inference(flattening,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.43    inference(nnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.21/0.43  fof(f173,plain,(
% 0.21/0.43    r1_tarski(sK0,k2_tarski(sK1,sK2)) | ~spl3_1),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f172])).
% 0.21/0.43  fof(f172,plain,(
% 0.21/0.43    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_tarski(sK1,sK2)) | ~spl3_1),
% 0.21/0.43    inference(superposition,[],[f32,f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | ~spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f41])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.43    inference(nnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.21/0.43  fof(f164,plain,(
% 0.21/0.43    spl3_1 | ~spl3_4),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f155])).
% 0.21/0.43  fof(f155,plain,(
% 0.21/0.43    $false | (spl3_1 | ~spl3_4)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f43,f139,f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f139,plain,(
% 0.21/0.43    ( ! [X5] : (r1_tarski(sK0,k2_tarski(sK1,X5))) ) | ~spl3_4),
% 0.21/0.43    inference(superposition,[],[f38,f56])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    sK0 = k1_tarski(sK1) | ~spl3_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f55])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X2,X1] : (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))) )),
% 0.21/0.43    inference(equality_resolution,[],[f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f41])).
% 0.21/0.43  fof(f131,plain,(
% 0.21/0.43    spl3_1 | ~spl3_5),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f119])).
% 0.21/0.43  fof(f119,plain,(
% 0.21/0.43    $false | (spl3_1 | ~spl3_5)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f39,f114,f33])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK1,sK2)) | (spl3_1 | ~spl3_5)),
% 0.21/0.43    inference(backward_demodulation,[],[f43,f61])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    k1_xboole_0 = sK0 | ~spl3_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f60])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X2))) )),
% 0.21/0.43    inference(equality_resolution,[],[f26])).
% 0.21/0.43  % (20544)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    spl3_1 | ~spl3_3),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f106])).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    $false | (spl3_1 | ~spl3_3)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f43,f91,f33])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    ( ! [X6] : (r1_tarski(sK0,k2_tarski(X6,sK2))) ) | ~spl3_3),
% 0.21/0.43    inference(superposition,[],[f37,f51])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    sK0 = k1_tarski(sK2) | ~spl3_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f50])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ( ! [X2,X1] : (r1_tarski(k1_tarski(X2),k2_tarski(X1,X2))) )),
% 0.21/0.43    inference(equality_resolution,[],[f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    spl3_1 | ~spl3_2),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f78])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    $false | (spl3_1 | ~spl3_2)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f69,f76,f33])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (spl3_1 | ~spl3_2)),
% 0.21/0.43    inference(forward_demodulation,[],[f43,f46])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    sK0 = k2_tarski(sK1,sK2) | ~spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f45])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    r1_tarski(sK0,sK0) | ~spl3_2),
% 0.21/0.43    inference(superposition,[],[f36,f46])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2))) )),
% 0.21/0.43    inference(equality_resolution,[],[f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X2) != X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    spl3_1 | spl3_5 | spl3_4 | spl3_3 | spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f45,f50,f55,f60,f41])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)))) => (((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 0.21/0.43    inference(flattening,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 0.21/0.43    inference(nnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.43    inference(negated_conjecture,[],[f8])).
% 0.21/0.43  fof(f8,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    ~spl3_1 | ~spl3_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f21,f60,f41])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    ~spl3_1 | ~spl3_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f55,f41])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    sK0 != k1_tarski(sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ~spl3_1 | ~spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f50,f41])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    sK0 != k1_tarski(sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ~spl3_1 | ~spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f45,f41])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    sK0 != k2_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (20551)------------------------------
% 0.21/0.43  % (20551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (20551)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (20551)Memory used [KB]: 6140
% 0.21/0.43  % (20551)Time elapsed: 0.048 s
% 0.21/0.43  % (20551)------------------------------
% 0.21/0.43  % (20551)------------------------------
% 0.21/0.43  % (20540)Success in time 0.079 s
%------------------------------------------------------------------------------

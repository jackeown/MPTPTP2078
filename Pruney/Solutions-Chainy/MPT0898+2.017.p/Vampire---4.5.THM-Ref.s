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
% DateTime   : Thu Dec  3 12:59:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  66 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :  136 ( 215 expanded)
%              Number of equality atoms :  104 ( 179 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f77,f92])).

fof(f92,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f90,f83])).

fof(f83,plain,
    ( k1_xboole_0 != sK1
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f17,f41])).

fof(f41,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

% (6995)Refutation not found, incomplete strategy% (6995)------------------------------
% (6995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6995)Termination reason: Refutation not found, incomplete strategy

fof(f39,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f17,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f11])).

% (6995)Memory used [KB]: 10490
% (6995)Time elapsed: 0.100 s
% (6995)------------------------------
% (6995)------------------------------
fof(f11,plain,
    ( sK1 != sK2
    & k4_zfmisc_1(sK1,sK1,sK1,sK1) = k4_zfmisc_1(sK2,sK2,sK2,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f5,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) )
   => ( sK1 != sK2
      & k4_zfmisc_1(sK1,sK1,sK1,sK1) = k4_zfmisc_1(sK2,sK2,sK2,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).

fof(f90,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | ~ spl3_2 ),
    inference(superposition,[],[f18,f44])).

fof(f44,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK1,sK1,sK1,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_2
  <=> k1_xboole_0 = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f77,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f69,f17])).

fof(f69,plain,
    ( sK1 = sK2
    | spl3_2 ),
    inference(resolution,[],[f64,f23])).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7)
      | X6 = X7 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X0 = X1
        & X2 = X3
        & X4 = X5
        & X6 = X7 )
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X7,X3,X6,X2,X5,X1,X4,X0] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | ~ sP0(X7,X3,X6,X2,X5,X1,X4,X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X7,X3,X6,X2,X5,X1,X4,X0] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | ~ sP0(X7,X3,X6,X2,X5,X1,X4,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f64,plain,
    ( sP0(sK1,sK2,sK1,sK2,sK1,sK2,sK1,sK2)
    | spl3_2 ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,
    ( ! [X2,X0,X3,X1] :
        ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK1,sK1,sK1,sK1)
        | sP0(X3,sK2,X2,sK2,X1,sK2,X0,sK2) )
    | spl3_2 ),
    inference(subsumption_resolution,[],[f47,f45])).

fof(f45,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK1,sK1,sK1,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK1,sK1,sK1,sK1)
      | k1_xboole_0 = k4_zfmisc_1(sK1,sK1,sK1,sK1)
      | sP0(X3,sK2,X2,sK2,X1,sK2,X0,sK2) ) ),
    inference(superposition,[],[f27,f16])).

fof(f16,plain,(
    k4_zfmisc_1(sK1,sK1,sK1,sK1) = k4_zfmisc_1(sK2,sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
      | sP0(X7,X3,X6,X2,X5,X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( sP0(X7,X3,X6,X2,X5,X1,X4,X0)
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(definition_folding,[],[f7,f8])).

fof(f7,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

fof(f46,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f37,f43,f39])).

fof(f37,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f32])).

fof(f32,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f18,f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:15:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (7015)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (7016)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (6996)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (6999)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (7019)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (6995)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (6999)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f46,f77,f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ~spl3_1 | ~spl3_2),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    $false | (~spl3_1 | ~spl3_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f90,f83])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | ~spl3_1),
% 0.21/0.51    inference(backward_demodulation,[],[f17,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f39])).
% 0.21/0.51  % (6995)Refutation not found, incomplete strategy% (6995)------------------------------
% 0.21/0.51  % (6995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6995)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    spl3_1 <=> k1_xboole_0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    sK1 != sK2),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  % (6995)Memory used [KB]: 10490
% 0.21/0.51  % (6995)Time elapsed: 0.100 s
% 0.21/0.51  % (6995)------------------------------
% 0.21/0.51  % (6995)------------------------------
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    sK1 != sK2 & k4_zfmisc_1(sK1,sK1,sK1,sK1) = k4_zfmisc_1(sK2,sK2,sK2,sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f5,f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)) => (sK1 != sK2 & k4_zfmisc_1(sK1,sK1,sK1,sK1) = k4_zfmisc_1(sK2,sK2,sK2,sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f5,plain,(
% 0.21/0.51    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.21/0.51    inference(negated_conjecture,[],[f3])).
% 0.21/0.51  fof(f3,conjecture,(
% 0.21/0.51    ! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl3_2),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | ~spl3_2),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | ~spl3_2),
% 0.21/0.51    inference(superposition,[],[f18,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    k1_xboole_0 = k4_zfmisc_1(sK1,sK1,sK1,sK1) | ~spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    spl3_2 <=> k1_xboole_0 = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl3_2),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    $false | spl3_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f69,f17])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    sK1 = sK2 | spl3_2),
% 0.21/0.51    inference(resolution,[],[f64,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~sP0(X0,X1,X2,X3,X4,X5,X6,X7) | X6 = X7) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((X0 = X1 & X2 = X3 & X4 = X5 & X6 = X7) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7))),
% 0.21/0.51    inference(rectify,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X7,X3,X6,X2,X5,X1,X4,X0] : ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | ~sP0(X7,X3,X6,X2,X5,X1,X4,X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X7,X3,X6,X2,X5,X1,X4,X0] : ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | ~sP0(X7,X3,X6,X2,X5,X1,X4,X0))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    sP0(sK1,sK2,sK1,sK2,sK1,sK2,sK1,sK2) | spl3_2),
% 0.21/0.51    inference(equality_resolution,[],[f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK1,sK1,sK1,sK1) | sP0(X3,sK2,X2,sK2,X1,sK2,X0,sK2)) ) | spl3_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f47,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    k1_xboole_0 != k4_zfmisc_1(sK1,sK1,sK1,sK1) | spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f43])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK1,sK1,sK1,sK1) | k1_xboole_0 = k4_zfmisc_1(sK1,sK1,sK1,sK1) | sP0(X3,sK2,X2,sK2,X1,sK2,X0,sK2)) )),
% 0.21/0.51    inference(superposition,[],[f27,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    k4_zfmisc_1(sK1,sK1,sK1,sK1) = k4_zfmisc_1(sK2,sK2,sK2,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | sP0(X7,X3,X6,X2,X5,X1,X4,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (sP0(X7,X3,X6,X2,X5,X1,X4,X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7))),
% 0.21/0.51    inference(definition_folding,[],[f7,f8])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7))),
% 0.21/0.51    inference(flattening,[],[f6])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    spl3_1 | ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f43,f39])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    k1_xboole_0 != k4_zfmisc_1(sK1,sK1,sK1,sK1) | k1_xboole_0 = sK2),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    k1_xboole_0 != k4_zfmisc_1(sK1,sK1,sK1,sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.21/0.51    inference(superposition,[],[f18,f16])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (6999)------------------------------
% 0.21/0.51  % (6999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6999)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (6999)Memory used [KB]: 6140
% 0.21/0.51  % (6999)Time elapsed: 0.096 s
% 0.21/0.51  % (6999)------------------------------
% 0.21/0.51  % (6999)------------------------------
% 0.21/0.51  % (6994)Success in time 0.146 s
%------------------------------------------------------------------------------

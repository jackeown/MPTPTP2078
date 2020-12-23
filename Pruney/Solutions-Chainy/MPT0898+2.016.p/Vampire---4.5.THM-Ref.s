%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  60 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :  127 ( 199 expanded)
%              Number of equality atoms :  107 ( 175 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f100,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f73,f95])).

fof(f95,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f93,f75])).

fof(f75,plain,
    ( k1_xboole_0 != sK0
    | ~ spl2_1 ),
    inference(backward_demodulation,[],[f13,f44])).

fof(f44,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f13,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( sK0 != sK1
    & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) )
   => ( sK0 != sK1
      & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

fof(f93,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | ~ spl2_1 ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | ~ spl2_1 ),
    inference(superposition,[],[f14,f76])).

fof(f76,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK0,sK0,sK0)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f74,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,k1_xboole_0) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f74,plain,
    ( k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl2_1 ),
    inference(backward_demodulation,[],[f12,f44])).

fof(f12,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f73,plain,(
    ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f71,f13])).

fof(f71,plain,
    ( sK0 = sK1
    | ~ spl2_3 ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,
    ( ! [X2,X0,X3,X1] :
        ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK0,sK0,sK0)
        | sK1 = X0 )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_3
  <=> ! [X1,X3,X0,X2] :
        ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK0,sK0,sK0)
        | sK1 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f53,plain,
    ( spl2_1
    | spl2_3 ),
    inference(avatar_split_clause,[],[f39,f51,f42])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK0,sK0,sK0)
      | k1_xboole_0 = sK1
      | sK1 = X0 ) ),
    inference(duplicate_literal_removal,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK0,sK0,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK1
      | sK1 = X0 ) ),
    inference(superposition,[],[f19,f12])).

fof(f19,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (12151)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.48  % (12154)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.48  % (12151)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (12175)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f53,f73,f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ~spl2_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    $false | ~spl2_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f93,f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 | ~spl2_1),
% 0.21/0.48    inference(backward_demodulation,[],[f13,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl2_1 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    sK0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)) => (sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f5,plain,(
% 0.21/0.48    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.21/0.48    inference(negated_conjecture,[],[f3])).
% 0.21/0.48  fof(f3,conjecture,(
% 0.21/0.48    ! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | ~spl2_1),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | ~spl2_1),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | ~spl2_1),
% 0.21/0.48    inference(superposition,[],[f14,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    k1_xboole_0 = k4_zfmisc_1(sK0,sK0,sK0,sK0) | ~spl2_1),
% 0.21/0.48    inference(forward_demodulation,[],[f74,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,k1_xboole_0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl2_1),
% 0.21/0.48    inference(backward_demodulation,[],[f12,f44])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ~spl2_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    $false | ~spl2_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f71,f13])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    sK0 = sK1 | ~spl2_3),
% 0.21/0.48    inference(equality_resolution,[],[f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK0,sK0,sK0) | sK1 = X0) ) | ~spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl2_3 <=> ! [X1,X3,X0,X2] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK0,sK0,sK0) | sK1 = X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl2_1 | spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f39,f51,f42])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1 | sK1 = X0) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | sK1 = X0) )),
% 0.21/0.48    inference(superposition,[],[f19,f12])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X0 = X4) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (12151)------------------------------
% 0.21/0.48  % (12151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12151)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (12151)Memory used [KB]: 10618
% 0.21/0.48  % (12151)Time elapsed: 0.077 s
% 0.21/0.48  % (12151)------------------------------
% 0.21/0.48  % (12151)------------------------------
% 0.21/0.49  % (12149)Success in time 0.131 s
%------------------------------------------------------------------------------

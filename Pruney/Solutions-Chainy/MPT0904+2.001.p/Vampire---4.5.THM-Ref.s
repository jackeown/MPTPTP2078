%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 132 expanded)
%              Number of leaves         :    9 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 324 expanded)
%              Number of equality atoms :    5 (  40 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f42,f44,f46,f48])).

fof(f48,plain,(
    ~ spl8_1 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f21,f40])).

fof(f40,plain,(
    ~ r1_xboole_0(sK0,sK4) ),
    inference(resolution,[],[f38,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f38,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f36,f14])).

fof(f36,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(resolution,[],[f17,f14])).

fof(f17,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f10,f16,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f13,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f10,plain,(
    ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ( r1_xboole_0(sK3,sK7)
      | r1_xboole_0(sK2,sK6)
      | r1_xboole_0(sK1,sK5)
      | r1_xboole_0(sK0,sK4) )
    & ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( r1_xboole_0(X3,X7)
          | r1_xboole_0(X2,X6)
          | r1_xboole_0(X1,X5)
          | r1_xboole_0(X0,X4) )
        & ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
   => ( ( r1_xboole_0(sK3,sK7)
        | r1_xboole_0(sK2,sK6)
        | r1_xboole_0(sK1,sK5)
        | r1_xboole_0(sK0,sK4) )
      & ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( r1_xboole_0(X3,X7)
        | r1_xboole_0(X2,X6)
        | r1_xboole_0(X1,X5)
        | r1_xboole_0(X0,X4) )
      & ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
       => ( ~ r1_xboole_0(X3,X7)
          & ~ r1_xboole_0(X2,X6)
          & ~ r1_xboole_0(X1,X5)
          & ~ r1_xboole_0(X0,X4) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
     => ( ~ r1_xboole_0(X3,X7)
        & ~ r1_xboole_0(X2,X6)
        & ~ r1_xboole_0(X1,X5)
        & ~ r1_xboole_0(X0,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_mcart_1)).

fof(f21,plain,
    ( r1_xboole_0(sK0,sK4)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl8_1
  <=> r1_xboole_0(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f46,plain,(
    ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f33,f35])).

fof(f35,plain,(
    ~ r1_xboole_0(sK3,sK7) ),
    inference(resolution,[],[f17,f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f33,plain,
    ( r1_xboole_0(sK3,sK7)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl8_4
  <=> r1_xboole_0(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f44,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f43])).

fof(f43,plain,
    ( $false
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f29,f37])).

fof(f37,plain,(
    ~ r1_xboole_0(sK2,sK6) ),
    inference(resolution,[],[f36,f15])).

fof(f29,plain,
    ( r1_xboole_0(sK2,sK6)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl8_3
  <=> r1_xboole_0(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f42,plain,(
    ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f41])).

fof(f41,plain,
    ( $false
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f39,f25])).

fof(f25,plain,
    ( r1_xboole_0(sK1,sK5)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl8_2
  <=> r1_xboole_0(sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f39,plain,(
    ~ r1_xboole_0(sK1,sK5) ),
    inference(resolution,[],[f38,f15])).

fof(f34,plain,
    ( spl8_1
    | spl8_2
    | spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f11,f31,f27,f23,f19])).

fof(f11,plain,
    ( r1_xboole_0(sK3,sK7)
    | r1_xboole_0(sK2,sK6)
    | r1_xboole_0(sK1,sK5)
    | r1_xboole_0(sK0,sK4) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (14898)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.45  % (14914)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.46  % (14912)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (14912)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f34,f42,f44,f46,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ~spl8_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    $false | ~spl8_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f21,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ~r1_xboole_0(sK0,sK4)),
% 0.20/0.47    inference(resolution,[],[f38,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ~r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5))),
% 0.20/0.47    inference(resolution,[],[f36,f14])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ~r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 0.20/0.47    inference(resolution,[],[f17,f14])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ~r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.20/0.47    inference(definition_unfolding,[],[f10,f16,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f13,f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ~r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    (r1_xboole_0(sK3,sK7) | r1_xboole_0(sK2,sK6) | r1_xboole_0(sK1,sK5) | r1_xboole_0(sK0,sK4)) & ~r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f6,f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((r1_xboole_0(X3,X7) | r1_xboole_0(X2,X6) | r1_xboole_0(X1,X5) | r1_xboole_0(X0,X4)) & ~r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) => ((r1_xboole_0(sK3,sK7) | r1_xboole_0(sK2,sK6) | r1_xboole_0(sK1,sK5) | r1_xboole_0(sK0,sK4)) & ~r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((r1_xboole_0(X3,X7) | r1_xboole_0(X2,X6) | r1_xboole_0(X1,X5) | r1_xboole_0(X0,X4)) & ~r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (~r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) => (~r1_xboole_0(X3,X7) & ~r1_xboole_0(X2,X6) & ~r1_xboole_0(X1,X5) & ~r1_xboole_0(X0,X4)))),
% 0.20/0.47    inference(negated_conjecture,[],[f4])).
% 0.20/0.47  fof(f4,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (~r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) => (~r1_xboole_0(X3,X7) & ~r1_xboole_0(X2,X6) & ~r1_xboole_0(X1,X5) & ~r1_xboole_0(X0,X4)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_mcart_1)).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    r1_xboole_0(sK0,sK4) | ~spl8_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    spl8_1 <=> r1_xboole_0(sK0,sK4)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ~spl8_4),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    $false | ~spl8_4),
% 0.20/0.47    inference(subsumption_resolution,[],[f33,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ~r1_xboole_0(sK3,sK7)),
% 0.20/0.47    inference(resolution,[],[f17,f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    r1_xboole_0(sK3,sK7) | ~spl8_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    spl8_4 <=> r1_xboole_0(sK3,sK7)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ~spl8_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    $false | ~spl8_3),
% 0.20/0.47    inference(subsumption_resolution,[],[f29,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ~r1_xboole_0(sK2,sK6)),
% 0.20/0.47    inference(resolution,[],[f36,f15])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    r1_xboole_0(sK2,sK6) | ~spl8_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    spl8_3 <=> r1_xboole_0(sK2,sK6)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ~spl8_2),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    $false | ~spl8_2),
% 0.20/0.47    inference(subsumption_resolution,[],[f39,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    r1_xboole_0(sK1,sK5) | ~spl8_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    spl8_2 <=> r1_xboole_0(sK1,sK5)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ~r1_xboole_0(sK1,sK5)),
% 0.20/0.47    inference(resolution,[],[f38,f15])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    spl8_1 | spl8_2 | spl8_3 | spl8_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f11,f31,f27,f23,f19])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    r1_xboole_0(sK3,sK7) | r1_xboole_0(sK2,sK6) | r1_xboole_0(sK1,sK5) | r1_xboole_0(sK0,sK4)),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (14912)------------------------------
% 0.20/0.47  % (14912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (14912)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (14912)Memory used [KB]: 6140
% 0.20/0.47  % (14912)Time elapsed: 0.009 s
% 0.20/0.47  % (14912)------------------------------
% 0.20/0.47  % (14912)------------------------------
% 0.20/0.47  % (14902)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (14913)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (14897)Success in time 0.116 s
%------------------------------------------------------------------------------

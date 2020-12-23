%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 235 expanded)
%              Number of leaves         :   11 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  245 (1200 expanded)
%              Number of equality atoms :   32 ( 145 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f48,f54,f80,f82,f84,f86,f105,f107,f109,f111,f114])).

fof(f114,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f112,f23])).

fof(f23,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f112,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f42,f45])).

fof(f45,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f42,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f111,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f96,f23])).

fof(f96,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f63,f45])).

fof(f63,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_xboole_0(sK0,X0),sK0)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f57,f53,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f34,f36])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

fof(f53,plain,
    ( r2_hidden(sK1(sK0),sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_3
  <=> r2_hidden(sK1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f57,plain,
    ( ! [X0] : r2_hidden(sK1(sK0),k2_xboole_0(sK0,X0))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f53,f36])).

fof(f109,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f95,f23])).

fof(f95,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f62,f45])).

fof(f62,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_xboole_0(X0,sK0),sK0)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f55,f53,f38])).

fof(f55,plain,
    ( ! [X0] : r2_hidden(sK1(sK0),k2_xboole_0(X0,sK0))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f53,f35])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

% (11698)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f107,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f94,f23])).

fof(f94,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f61,f45])).

fof(f61,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f53,f53,f38])).

fof(f105,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f87,f79])).

fof(f79,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f38,f23])).

fof(f87,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f53,f45])).

fof(f86,plain,
    ( ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f61,f41])).

fof(f41,plain,
    ( r1_xboole_0(sK0,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f84,plain,
    ( ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f73,f53])).

fof(f73,plain,
    ( ~ r2_hidden(sK1(sK0),sK0)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f53,f41,f38])).

fof(f82,plain,
    ( ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f74,f53])).

fof(f74,plain,
    ( ~ r2_hidden(sK1(sK0),sK0)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f53,f41,f38])).

fof(f80,plain,
    ( ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f53,f53,f41,f38])).

fof(f54,plain,
    ( spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f49,f44,f51])).

fof(f49,plain,
    ( r2_hidden(sK1(sK0),sK0)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f46,f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f8,f12])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f46,plain,
    ( k1_xboole_0 != sK0
    | spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f48,plain,
    ( spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f22,f40,f44])).

fof(f22,plain,
    ( r1_xboole_0(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( r1_xboole_0(sK0,sK0)
      & k1_xboole_0 != sK0 )
    | ( k1_xboole_0 = sK0
      & ~ r1_xboole_0(sK0,sK0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
        | ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) )
   => ( ( r1_xboole_0(sK0,sK0)
        & k1_xboole_0 != sK0 )
      | ( k1_xboole_0 = sK0
        & ~ r1_xboole_0(sK0,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ( r1_xboole_0(X0,X0)
        & k1_xboole_0 != X0 )
      | ( k1_xboole_0 = X0
        & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ~ ( r1_xboole_0(X0,X0)
            & k1_xboole_0 != X0 )
        & ~ ( k1_xboole_0 = X0
            & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f47,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f19,f44,f40])).

fof(f19,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_xboole_0(sK0,sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:56:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (11702)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (11702)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f47,f48,f54,f80,f82,f84,f86,f105,f107,f109,f111,f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    spl3_1 | ~spl3_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f113])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    $false | (spl3_1 | ~spl3_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f112,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (spl3_1 | ~spl3_2)),
% 0.21/0.48    inference(forward_demodulation,[],[f42,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl3_2 <=> k1_xboole_0 = sK0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ~r1_xboole_0(sK0,sK0) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    spl3_1 <=> r1_xboole_0(sK0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ~spl3_2 | ~spl3_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f110])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    $false | (~spl3_2 | ~spl3_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f96,f23])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0)) ) | (~spl3_2 | ~spl3_3)),
% 0.21/0.49    inference(backward_demodulation,[],[f63,f45])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_xboole_0(k2_xboole_0(sK0,X0),sK0)) ) | ~spl3_3),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f57,f53,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f34,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.49    inference(rectify,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    r2_hidden(sK1(sK0),sK0) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl3_3 <=> r2_hidden(sK1(sK0),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK1(sK0),k2_xboole_0(sK0,X0))) ) | ~spl3_3),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f53,f36])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ~spl3_2 | ~spl3_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f108])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    $false | (~spl3_2 | ~spl3_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f95,f23])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0)) ) | (~spl3_2 | ~spl3_3)),
% 0.21/0.49    inference(backward_demodulation,[],[f62,f45])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_xboole_0(k2_xboole_0(X0,sK0),sK0)) ) | ~spl3_3),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f55,f53,f38])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK1(sK0),k2_xboole_0(X0,sK0))) ) | ~spl3_3),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f53,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  % (11698)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    ~spl3_2 | ~spl3_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f106])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    $false | (~spl3_2 | ~spl3_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f94,f23])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl3_2 | ~spl3_3)),
% 0.21/0.49    inference(backward_demodulation,[],[f61,f45])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ~r1_xboole_0(sK0,sK0) | ~spl3_3),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f53,f53,f38])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ~spl3_2 | ~spl3_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    $false | (~spl3_2 | ~spl3_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f87,f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(condensation,[],[f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(resolution,[],[f38,f23])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | (~spl3_2 | ~spl3_3)),
% 0.21/0.49    inference(backward_demodulation,[],[f53,f45])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    $false | (~spl3_1 | ~spl3_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f61,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    r1_xboole_0(sK0,sK0) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f40])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    $false | (~spl3_1 | ~spl3_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f73,f53])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ~r2_hidden(sK1(sK0),sK0) | (~spl3_1 | ~spl3_3)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f53,f41,f38])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    $false | (~spl3_1 | ~spl3_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f74,f53])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ~r2_hidden(sK1(sK0),sK0) | (~spl3_1 | ~spl3_3)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f53,f41,f38])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    $false | (~spl3_1 | ~spl3_3)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f53,f53,f41,f38])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl3_3 | spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f49,f44,f51])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    r2_hidden(sK1(sK0),sK0) | spl3_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f46,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f8,f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    k1_xboole_0 != sK0 | spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f44])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    spl3_2 | spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f40,f44])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    r1_xboole_0(sK0,sK0) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    (r1_xboole_0(sK0,sK0) & k1_xboole_0 != sK0) | (k1_xboole_0 = sK0 & ~r1_xboole_0(sK0,sK0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0] : ((r1_xboole_0(X0,X0) & k1_xboole_0 != X0) | (k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0))) => ((r1_xboole_0(sK0,sK0) & k1_xboole_0 != sK0) | (k1_xboole_0 = sK0 & ~r1_xboole_0(sK0,sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0] : ((r1_xboole_0(X0,X0) & k1_xboole_0 != X0) | (k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f19,f44,f40])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    k1_xboole_0 != sK0 | ~r1_xboole_0(sK0,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (11702)------------------------------
% 0.21/0.49  % (11702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11702)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (11702)Memory used [KB]: 1663
% 0.21/0.49  % (11702)Time elapsed: 0.066 s
% 0.21/0.49  % (11702)------------------------------
% 0.21/0.49  % (11702)------------------------------
% 0.21/0.49  % (11694)Success in time 0.132 s
%------------------------------------------------------------------------------

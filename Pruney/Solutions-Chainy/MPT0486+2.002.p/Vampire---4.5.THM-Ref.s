%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:18 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   46 (  59 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :   15
%              Number of atoms          :  155 ( 180 expanded)
%              Number of equality atoms :   42 (  54 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(subsumption_resolution,[],[f82,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f82,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK5(k1_xboole_0,k1_xboole_0))),k1_xboole_0) ),
    inference(resolution,[],[f77,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f77,plain,(
    r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK5(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f75,f30])).

fof(f75,plain,
    ( r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK5(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = k2_xboole_0(k1_tarski(sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[],[f72,f41])).

fof(f72,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK5(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[],[f70,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | X0 != X1
        | ~ r2_hidden(X1,X2) )
      & ( ( X0 = X1
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X3,X2,X0] :
      ( ( sP0(X3,X2,X0)
        | X2 != X3
        | ~ r2_hidden(X2,X0) )
      & ( ( X2 = X3
          & r2_hidden(X2,X0) )
        | ~ sP0(X3,X2,X0) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X3,X2,X0] :
      ( ( sP0(X3,X2,X0)
        | X2 != X3
        | ~ r2_hidden(X2,X0) )
      & ( ( X2 = X3
          & r2_hidden(X2,X0) )
        | ~ sP0(X3,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X3,X2,X0] :
      ( sP0(X3,X2,X0)
    <=> ( X2 = X3
        & r2_hidden(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f70,plain,
    ( sP0(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK5(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f69,f30])).

fof(f69,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_tarski(sK3(k1_xboole_0)),k1_xboole_0)
    | sP0(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK5(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k2_xboole_0(k1_tarski(sK3(X0)),X0) = X0
      | sP0(sK5(k1_xboole_0,X0),sK4(k1_xboole_0,X0),k1_xboole_0)
      | r2_hidden(k4_tarski(sK4(k1_xboole_0,X0),sK5(k1_xboole_0,X0)),X0) ) ),
    inference(resolution,[],[f48,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | sP0(sK5(X0,X1),sK4(X0,X1),X0)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(sK5(X0,X1),sK4(X0,X1),X0)
            | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
          & ( sP0(sK5(X0,X1),sK4(X0,X1),X0)
            | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) ) ) )
      & ( ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),X1)
              | ~ sP0(X5,X4,X0) )
            & ( sP0(X5,X4,X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ sP0(X3,X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( sP0(X3,X2,X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ sP0(sK5(X0,X1),sK4(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & ( sP0(sK5(X0,X1),sK4(X0,X1),X0)
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2,X3] :
            ( ( ~ sP0(X3,X2,X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( sP0(X3,X2,X0)
              | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
      & ( ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),X1)
              | ~ sP0(X5,X4,X0) )
            & ( sP0(X5,X4,X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2,X3] :
            ( ( ~ sP0(X3,X2,X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( sP0(X3,X2,X0)
              | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
      & ( ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ sP0(X3,X2,X0) )
            & ( sP0(X3,X2,X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X1)
        <=> sP0(X3,X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f48,plain,(
    ! [X0] :
      ( ~ sP1(k1_xboole_0,X0)
      | k1_xboole_0 != X0
      | k2_xboole_0(k1_tarski(sK3(X0)),X0) = X0 ) ),
    inference(resolution,[],[f46,f41])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | ~ sP1(k1_xboole_0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(resolution,[],[f45,f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != X0
      | ~ sP1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f44,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f10,f14,f13,f12])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ( k6_relat_1(X0) = X1
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(f44,plain,(
    ! [X0] :
      ( ~ sP2(X0,k1_xboole_0)
      | ~ sP1(k1_xboole_0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f27,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X1) = X0
      | ~ sP1(X1,X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X1) = X0
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | k6_relat_1(X1) != X0 ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ( ( k6_relat_1(X0) = X1
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | k6_relat_1(X0) != X1 ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f27,plain,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f6])).

fof(f6,negated_conjecture,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:14:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.44  % (30056)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.19/0.46  % (30047)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.47  % (30055)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.47  % (30039)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.47  % (30039)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f84,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(subsumption_resolution,[],[f82,f30])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.19/0.47    inference(cnf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.19/0.47  fof(f82,plain,(
% 0.19/0.47    k1_xboole_0 = k2_xboole_0(k1_tarski(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK5(k1_xboole_0,k1_xboole_0))),k1_xboole_0)),
% 0.19/0.47    inference(resolution,[],[f77,f41])).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f11])).
% 0.19/0.47  fof(f11,plain,(
% 0.19/0.47    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.19/0.47  fof(f77,plain,(
% 0.19/0.47    r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK5(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.19/0.47    inference(subsumption_resolution,[],[f75,f30])).
% 0.19/0.47  fof(f75,plain,(
% 0.19/0.47    r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK5(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | k1_xboole_0 = k2_xboole_0(k1_tarski(sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.19/0.47    inference(resolution,[],[f72,f41])).
% 0.19/0.47  fof(f72,plain,(
% 0.19/0.47    r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK5(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.19/0.47    inference(resolution,[],[f70,f37])).
% 0.19/0.47  fof(f37,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~sP0(X0,X1,X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | X0 != X1 | ~r2_hidden(X1,X2)) & ((X0 = X1 & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 0.19/0.47    inference(rectify,[],[f25])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ! [X3,X2,X0] : ((sP0(X3,X2,X0) | X2 != X3 | ~r2_hidden(X2,X0)) & ((X2 = X3 & r2_hidden(X2,X0)) | ~sP0(X3,X2,X0)))),
% 0.19/0.47    inference(flattening,[],[f24])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ! [X3,X2,X0] : ((sP0(X3,X2,X0) | (X2 != X3 | ~r2_hidden(X2,X0))) & ((X2 = X3 & r2_hidden(X2,X0)) | ~sP0(X3,X2,X0)))),
% 0.19/0.47    inference(nnf_transformation,[],[f12])).
% 0.19/0.47  fof(f12,plain,(
% 0.19/0.47    ! [X3,X2,X0] : (sP0(X3,X2,X0) <=> (X2 = X3 & r2_hidden(X2,X0)))),
% 0.19/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.47  fof(f70,plain,(
% 0.19/0.47    sP0(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK5(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.19/0.47    inference(subsumption_resolution,[],[f69,f30])).
% 0.19/0.47  fof(f69,plain,(
% 0.19/0.47    k1_xboole_0 = k2_xboole_0(k1_tarski(sK3(k1_xboole_0)),k1_xboole_0) | sP0(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK5(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.19/0.47    inference(equality_resolution,[],[f57])).
% 0.19/0.47  fof(f57,plain,(
% 0.19/0.47    ( ! [X0] : (k1_xboole_0 != X0 | k2_xboole_0(k1_tarski(sK3(X0)),X0) = X0 | sP0(sK5(k1_xboole_0,X0),sK4(k1_xboole_0,X0),k1_xboole_0) | r2_hidden(k4_tarski(sK4(k1_xboole_0,X0),sK5(k1_xboole_0,X0)),X0)) )),
% 0.19/0.47    inference(resolution,[],[f48,f35])).
% 0.19/0.47  fof(f35,plain,(
% 0.19/0.47    ( ! [X0,X1] : (sP1(X0,X1) | sP0(sK5(X0,X1),sK4(X0,X1),X0) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(sK5(X0,X1),sK4(X0,X1),X0) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & (sP0(sK5(X0,X1),sK4(X0,X1),X0) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~sP0(X5,X4,X0)) & (sP0(X5,X4,X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~sP1(X0,X1)))),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ! [X1,X0] : (? [X2,X3] : ((~sP0(X3,X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (sP0(X3,X2,X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~sP0(sK5(X0,X1),sK4(X0,X1),X0) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & (sP0(sK5(X0,X1),sK4(X0,X1),X0) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1))))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0,X1] : ((sP1(X0,X1) | ? [X2,X3] : ((~sP0(X3,X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (sP0(X3,X2,X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~sP0(X5,X4,X0)) & (sP0(X5,X4,X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~sP1(X0,X1)))),
% 0.19/0.47    inference(rectify,[],[f20])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ! [X0,X1] : ((sP1(X0,X1) | ? [X2,X3] : ((~sP0(X3,X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (sP0(X3,X2,X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~sP0(X3,X2,X0)) & (sP0(X3,X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~sP1(X0,X1)))),
% 0.19/0.47    inference(nnf_transformation,[],[f13])).
% 0.19/0.47  fof(f13,plain,(
% 0.19/0.47    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> sP0(X3,X2,X0)))),
% 0.19/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    ( ! [X0] : (~sP1(k1_xboole_0,X0) | k1_xboole_0 != X0 | k2_xboole_0(k1_tarski(sK3(X0)),X0) = X0) )),
% 0.19/0.47    inference(resolution,[],[f46,f41])).
% 0.19/0.47  fof(f46,plain,(
% 0.19/0.47    ( ! [X0] : (r2_hidden(sK3(X0),X0) | ~sP1(k1_xboole_0,X0) | k1_xboole_0 != X0) )),
% 0.19/0.47    inference(resolution,[],[f45,f28])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f16])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f9,plain,(
% 0.19/0.47    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.19/0.47    inference(unused_predicate_definition_removal,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.19/0.47  fof(f45,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != X0 | ~sP1(k1_xboole_0,X0)) )),
% 0.19/0.47    inference(resolution,[],[f44,f40])).
% 0.19/0.47  fof(f40,plain,(
% 0.19/0.47    ( ! [X0,X1] : (sP2(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f15])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    ! [X0,X1] : (sP2(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(definition_folding,[],[f10,f14,f13,f12])).
% 0.19/0.47  fof(f14,plain,(
% 0.19/0.47    ! [X1,X0] : ((k6_relat_1(X0) = X1 <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 0.19/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.19/0.47  fof(f10,plain,(
% 0.19/0.47    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).
% 0.19/0.47  fof(f44,plain,(
% 0.19/0.47    ( ! [X0] : (~sP2(X0,k1_xboole_0) | ~sP1(k1_xboole_0,X0) | k1_xboole_0 != X0) )),
% 0.19/0.47    inference(superposition,[],[f27,f32])).
% 0.19/0.47  fof(f32,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k6_relat_1(X1) = X0 | ~sP1(X1,X0) | ~sP2(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X0,X1] : (((k6_relat_1(X1) = X0 | ~sP1(X1,X0)) & (sP1(X1,X0) | k6_relat_1(X1) != X0)) | ~sP2(X0,X1))),
% 0.19/0.47    inference(rectify,[],[f18])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    ! [X1,X0] : (((k6_relat_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k6_relat_1(X0) != X1)) | ~sP2(X1,X0))),
% 0.19/0.47    inference(nnf_transformation,[],[f14])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    k1_xboole_0 != k6_relat_1(k1_xboole_0)),
% 0.19/0.47    inference(cnf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,plain,(
% 0.19/0.47    k1_xboole_0 != k6_relat_1(k1_xboole_0)),
% 0.19/0.47    inference(flattening,[],[f6])).
% 0.19/0.47  fof(f6,negated_conjecture,(
% 0.19/0.47    ~k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.19/0.47    inference(negated_conjecture,[],[f5])).
% 0.19/0.47  fof(f5,conjecture,(
% 0.19/0.47    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (30039)------------------------------
% 0.19/0.47  % (30039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (30039)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (30039)Memory used [KB]: 1663
% 0.19/0.47  % (30039)Time elapsed: 0.079 s
% 0.19/0.47  % (30039)------------------------------
% 0.19/0.47  % (30039)------------------------------
% 0.19/0.48  % (30030)Success in time 0.128 s
%------------------------------------------------------------------------------

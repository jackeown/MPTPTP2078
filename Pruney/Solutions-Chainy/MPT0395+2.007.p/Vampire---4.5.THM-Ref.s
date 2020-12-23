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
% DateTime   : Thu Dec  3 12:46:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 100 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :   17
%              Number of atoms          :  215 ( 384 expanded)
%              Number of equality atoms :   15 (  30 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(subsumption_resolution,[],[f135,f34])).

fof(f34,plain,(
    ~ r1_setfam_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_setfam_1(sK3,sK4)
    & r1_tarski(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f7,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ~ r1_setfam_1(X0,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_setfam_1(sK3,sK4)
      & r1_tarski(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_setfam_1(X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).

fof(f135,plain,(
    r1_setfam_1(sK3,sK4) ),
    inference(resolution,[],[f134,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ~ sP0(X1,X0) )
      & ( sP0(X1,X0)
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> sP0(X1,X0) ) ),
    inference(definition_folding,[],[f8,f9])).

fof(f9,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f134,plain,(
    sP0(sK4,sK3) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,
    ( sP0(sK4,sK3)
    | sP0(sK4,sK3) ),
    inference(resolution,[],[f131,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK5(X0,X1),X3)
              | ~ r2_hidden(X3,X0) )
          & r2_hidden(sK5(X0,X1),X1) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK6(X0,X4))
              & r2_hidden(sK6(X0,X4),X0) )
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f19,f21,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK5(X0,X1),X3)
            | ~ r2_hidden(X3,X0) )
        & r2_hidden(sK5(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X0) )
     => ( r1_tarski(X4,sK6(X0,X4))
        & r2_hidden(sK6(X0,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X0) )
            & r2_hidden(X2,X1) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X0) )
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK4,X0),sK3)
      | sP0(sK4,X0) ) ),
    inference(resolution,[],[f128,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f41,f55])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(sK5(X0,X1),X3)
      | sP0(X0,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f128,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK4)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f126,f33])).

fof(f33,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f124,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X1,X3,X0] :
      ( ( sP1(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP1(X1,X3,X0) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X1,X3,X0] :
      ( ( sP1(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP1(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X1,X3,X0] :
      ( sP1(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f124,plain,(
    ! [X4,X5,X3] :
      ( ~ sP1(X3,X4,X5)
      | ~ r1_tarski(X5,X3) ) ),
    inference(subsumption_resolution,[],[f99,f107])).

fof(f107,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f105])).

fof(f105,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f96,f55])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f91,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f91,plain,(
    ! [X4,X5,X3] :
      ( sP1(X4,X3,X5)
      | ~ r2_hidden(X3,k1_xboole_0)
      | ~ r1_tarski(X5,X4) ) ),
    inference(resolution,[],[f46,f60])).

fof(f60,plain,(
    ! [X2,X3] :
      ( sP2(X2,X3,k1_xboole_0)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f57,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] : sP2(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f12,f11])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP1(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ sP1(X1,sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sP1(X1,sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X4,X0) )
            & ( sP1(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP1(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP1(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP1(X1,sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sP1(X1,sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X4,X0) )
            & ( sP1(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP1(X1,X3,X0) )
            & ( sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f99,plain,(
    ! [X4,X5,X3] :
      ( ~ sP1(X3,X4,X5)
      | r2_hidden(X4,k1_xboole_0)
      | ~ r1_tarski(X5,X3) ) ),
    inference(resolution,[],[f47,f60])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ sP1(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (4272)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.44  % (4264)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.47  % (4286)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.48  % (4269)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.48  % (4268)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.48  % (4269)Refutation not found, incomplete strategy% (4269)------------------------------
% 0.20/0.48  % (4269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (4273)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.49  % (4277)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (4269)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (4269)Memory used [KB]: 10618
% 0.20/0.49  % (4269)Time elapsed: 0.087 s
% 0.20/0.49  % (4269)------------------------------
% 0.20/0.49  % (4269)------------------------------
% 0.20/0.49  % (4266)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (4280)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.49  % (4267)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (4276)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (4267)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f135,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ~r1_setfam_1(sK3,sK4)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ~r1_setfam_1(sK3,sK4) & r1_tarski(sK3,sK4)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f7,f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0,X1] : (~r1_setfam_1(X0,X1) & r1_tarski(X0,X1)) => (~r1_setfam_1(sK3,sK4) & r1_tarski(sK3,sK4))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f7,plain,(
% 0.20/0.50    ? [X0,X1] : (~r1_setfam_1(X0,X1) & r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 0.20/0.50    inference(negated_conjecture,[],[f5])).
% 0.20/0.50  fof(f5,conjecture,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    r1_setfam_1(sK3,sK4)),
% 0.20/0.50    inference(resolution,[],[f134,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~sP0(X1,X0) | r1_setfam_1(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~r1_setfam_1(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> sP0(X1,X0))),
% 0.20/0.50    inference(definition_folding,[],[f8,f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    sP0(sK4,sK3)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f133])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    sP0(sK4,sK3) | sP0(sK4,sK3)),
% 0.20/0.50    inference(resolution,[],[f131,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | sP0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (~r1_tarski(sK5(X0,X1),X3) | ~r2_hidden(X3,X0)) & r2_hidden(sK5(X0,X1),X1))) & (! [X4] : ((r1_tarski(X4,sK6(X0,X4)) & r2_hidden(sK6(X0,X4),X0)) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f19,f21,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X0)) & r2_hidden(X2,X1)) => (! [X3] : (~r1_tarski(sK5(X0,X1),X3) | ~r2_hidden(X3,X0)) & r2_hidden(sK5(X0,X1),X1)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X4,X0] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X0)) => (r1_tarski(X4,sK6(X0,X4)) & r2_hidden(sK6(X0,X4),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X0)) & r2_hidden(X2,X1))) & (! [X4] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X0)) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.20/0.50    inference(rectify,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~sP0(X1,X0)))),
% 0.20/0.50    inference(nnf_transformation,[],[f9])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK5(sK4,X0),sK3) | sP0(sK4,X0)) )),
% 0.20/0.50    inference(resolution,[],[f128,f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X0) | sP0(X0,X1)) )),
% 0.20/0.50    inference(resolution,[],[f41,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (~r1_tarski(sK5(X0,X1),X3) | sP0(X0,X1) | ~r2_hidden(X3,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(X0,sK4) | ~r2_hidden(X0,sK3)) )),
% 0.20/0.50    inference(resolution,[],[f126,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    r1_tarski(sK3,sK4)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.50    inference(resolution,[],[f124,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP1(X0,X1,X2)))),
% 0.20/0.50    inference(rectify,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X1,X3,X0] : ((sP1(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP1(X1,X3,X0)))),
% 0.20/0.50    inference(flattening,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X1,X3,X0] : ((sP1(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP1(X1,X3,X0)))),
% 0.20/0.50    inference(nnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X1,X3,X0] : (sP1(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    ( ! [X4,X5,X3] : (~sP1(X3,X4,X5) | ~r1_tarski(X5,X3)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f99,f107])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(condensation,[],[f105])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ( ! [X2,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X2)) )),
% 0.20/0.50    inference(resolution,[],[f96,f55])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X2)) )),
% 0.20/0.50    inference(resolution,[],[f91,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    ( ! [X4,X5,X3] : (sP1(X4,X3,X5) | ~r2_hidden(X3,k1_xboole_0) | ~r1_tarski(X5,X4)) )),
% 0.20/0.50    inference(resolution,[],[f46,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X2,X3] : (sP2(X2,X3,k1_xboole_0) | ~r1_tarski(X2,X3)) )),
% 0.20/0.50    inference(superposition,[],[f57,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.50    inference(nnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sP2(X0,X1,k4_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(equality_resolution,[],[f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.50    inference(nnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 0.20/0.50    inference(definition_folding,[],[f1,f12,f11])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X1,X3,X0)))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | sP1(X1,X4,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP1(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X4,X0)) & (sP1(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f26,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X2,X1,X0] : (? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP1(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP1(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X4,X0)) & (sP1(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.20/0.50    inference(rectify,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP1(X1,X3,X0)) & (sP1(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP2(X0,X1,X2)))),
% 0.20/0.50    inference(nnf_transformation,[],[f12])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ( ! [X4,X5,X3] : (~sP1(X3,X4,X5) | r2_hidden(X4,k1_xboole_0) | ~r1_tarski(X5,X3)) )),
% 0.20/0.50    inference(resolution,[],[f47,f60])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~sP1(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (4267)------------------------------
% 0.20/0.50  % (4267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (4267)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (4267)Memory used [KB]: 6140
% 0.20/0.50  % (4267)Time elapsed: 0.096 s
% 0.20/0.50  % (4267)------------------------------
% 0.20/0.50  % (4267)------------------------------
% 0.20/0.50  % (4262)Success in time 0.144 s
%------------------------------------------------------------------------------

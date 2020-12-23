%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:09 EST 2020

% Result     : Theorem 1.85s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 589 expanded)
%              Number of leaves         :   12 ( 164 expanded)
%              Depth                    :   26
%              Number of atoms          :  169 (1907 expanded)
%              Number of equality atoms :   47 ( 513 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f857,plain,(
    $false ),
    inference(subsumption_resolution,[],[f856,f245])).

fof(f245,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f237,f49])).

fof(f49,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f237,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f210,f76])).

fof(f76,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f210,plain,(
    ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f99,f208,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f208,plain,(
    ! [X4,X5] : ~ r2_hidden(X4,k11_relat_1(k1_xboole_0,X5)) ),
    inference(subsumption_resolution,[],[f206,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f206,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k11_relat_1(k1_xboole_0,X5))
      | k1_xboole_0 = k2_xboole_0(k1_tarski(k4_tarski(X5,X4)),k1_xboole_0) ) ),
    inference(resolution,[],[f109,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f109,plain,(
    ! [X12,X11] :
      ( r2_hidden(k4_tarski(X12,X11),k1_xboole_0)
      | ~ r2_hidden(X11,k11_relat_1(k1_xboole_0,X12)) ) ),
    inference(resolution,[],[f99,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f99,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f81,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f81,plain,(
    ! [X0] : v1_relat_1(k3_xboole_0(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f46,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f856,plain,(
    r2_hidden(sK5(sK1,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f843,f809])).

fof(f809,plain,(
    k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f803])).

fof(f803,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(resolution,[],[f614,f48])).

fof(f48,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f614,plain,(
    ! [X8] :
      ( r2_hidden(X8,k1_relat_1(sK1))
      | k1_xboole_0 = k11_relat_1(sK1,X8) ) ),
    inference(resolution,[],[f277,f188])).

fof(f188,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k11_relat_1(sK1,X5))
      | r2_hidden(X5,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f88,f75])).

fof(f75,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X12,X11] :
      ( r2_hidden(k4_tarski(X12,X11),sK1)
      | ~ r2_hidden(X11,k11_relat_1(sK1,X12)) ) ),
    inference(resolution,[],[f46,f68])).

fof(f277,plain,(
    ! [X3] :
      ( r2_hidden(sK3(k1_xboole_0,X3),X3)
      | k1_xboole_0 = X3 ) ),
    inference(forward_demodulation,[],[f276,f246])).

fof(f246,plain,(
    ! [X0] : k1_xboole_0 = k11_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f236,f49])).

fof(f236,plain,(
    ! [X0] : k1_relat_1(k1_xboole_0) = k11_relat_1(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f208,f210,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f276,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X3
      | r2_hidden(sK3(k11_relat_1(k1_xboole_0,X2),X3),X3) ) ),
    inference(forward_demodulation,[],[f265,f49])).

fof(f265,plain,(
    ! [X2,X3] :
      ( k1_relat_1(k1_xboole_0) = X3
      | r2_hidden(sK3(k11_relat_1(k1_xboole_0,X2),X3),X3) ) ),
    inference(backward_demodulation,[],[f228,f246])).

fof(f228,plain,(
    ! [X2,X3] :
      ( k1_relat_1(k11_relat_1(k1_xboole_0,X2)) = X3
      | r2_hidden(sK3(k11_relat_1(k1_xboole_0,X2),X3),X3) ) ),
    inference(resolution,[],[f208,f59])).

fof(f843,plain,(
    r2_hidden(sK5(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f46,f812,f67])).

fof(f812,plain,(
    r2_hidden(k4_tarski(sK0,sK5(sK1,sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f811,f76])).

fof(f811,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f810])).

fof(f810,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f47,f809])).

fof(f47,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:50:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (6915)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (6906)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (6910)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (6914)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (6906)Refutation not found, incomplete strategy% (6906)------------------------------
% 0.22/0.52  % (6906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6906)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (6906)Memory used [KB]: 10618
% 0.22/0.52  % (6906)Time elapsed: 0.081 s
% 0.22/0.52  % (6906)------------------------------
% 0.22/0.52  % (6906)------------------------------
% 0.22/0.52  % (6921)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (6908)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (6909)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.53  % (6920)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.54  % (6911)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.56  % (6925)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.56  % (6912)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.56  % (6916)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.57  % (6917)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (6919)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.57  % (6923)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.58  % (6922)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.58  % (6925)Refutation not found, incomplete strategy% (6925)------------------------------
% 0.22/0.58  % (6925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (6925)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (6925)Memory used [KB]: 10618
% 0.22/0.58  % (6925)Time elapsed: 0.157 s
% 0.22/0.58  % (6925)------------------------------
% 0.22/0.58  % (6925)------------------------------
% 0.22/0.58  % (6918)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.58  % (6913)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.59  % (6907)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.59  % (6905)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.85/0.60  % (6924)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.85/0.61  % (6920)Refutation found. Thanks to Tanya!
% 1.85/0.61  % SZS status Theorem for theBenchmark
% 1.85/0.61  % SZS output start Proof for theBenchmark
% 1.85/0.61  fof(f857,plain,(
% 1.85/0.61    $false),
% 1.85/0.61    inference(subsumption_resolution,[],[f856,f245])).
% 1.85/0.61  fof(f245,plain,(
% 1.85/0.61    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.85/0.61    inference(forward_demodulation,[],[f237,f49])).
% 1.85/0.61  fof(f49,plain,(
% 1.85/0.61    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.85/0.61    inference(cnf_transformation,[],[f12])).
% 1.85/0.61  fof(f12,axiom,(
% 1.85/0.61    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.85/0.61  fof(f237,plain,(
% 1.85/0.61    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 1.85/0.61    inference(unit_resulting_resolution,[],[f210,f76])).
% 1.85/0.61  fof(f76,plain,(
% 1.85/0.61    ( ! [X0,X5] : (~r2_hidden(X5,k1_relat_1(X0)) | r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)) )),
% 1.85/0.61    inference(equality_resolution,[],[f57])).
% 1.85/0.61  fof(f57,plain,(
% 1.85/0.61    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 1.85/0.61    inference(cnf_transformation,[],[f34])).
% 1.85/0.61  fof(f34,plain,(
% 1.85/0.61    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.85/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 1.85/0.61  fof(f31,plain,(
% 1.85/0.61    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.85/0.61    introduced(choice_axiom,[])).
% 1.85/0.61  fof(f32,plain,(
% 1.85/0.61    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 1.85/0.61    introduced(choice_axiom,[])).
% 1.85/0.61  fof(f33,plain,(
% 1.85/0.61    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 1.85/0.61    introduced(choice_axiom,[])).
% 1.85/0.61  fof(f30,plain,(
% 1.85/0.61    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.85/0.61    inference(rectify,[],[f29])).
% 1.85/0.61  fof(f29,plain,(
% 1.85/0.61    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.85/0.61    inference(nnf_transformation,[],[f7])).
% 1.85/0.61  fof(f7,axiom,(
% 1.85/0.61    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.85/0.61  fof(f210,plain,(
% 1.85/0.61    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_xboole_0)) )),
% 1.85/0.61    inference(unit_resulting_resolution,[],[f99,f208,f67])).
% 1.85/0.61  fof(f67,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0))) )),
% 1.85/0.61    inference(cnf_transformation,[],[f40])).
% 1.85/0.61  fof(f40,plain,(
% 1.85/0.61    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 1.85/0.61    inference(nnf_transformation,[],[f22])).
% 1.85/0.61  fof(f22,plain,(
% 1.85/0.61    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 1.85/0.61    inference(ennf_transformation,[],[f11])).
% 1.85/0.61  fof(f11,axiom,(
% 1.85/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 1.85/0.61  fof(f208,plain,(
% 1.85/0.61    ( ! [X4,X5] : (~r2_hidden(X4,k11_relat_1(k1_xboole_0,X5))) )),
% 1.85/0.61    inference(subsumption_resolution,[],[f206,f53])).
% 1.85/0.61  fof(f53,plain,(
% 1.85/0.61    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f5])).
% 1.85/0.61  fof(f5,axiom,(
% 1.85/0.61    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.85/0.61  fof(f206,plain,(
% 1.85/0.61    ( ! [X4,X5] : (~r2_hidden(X4,k11_relat_1(k1_xboole_0,X5)) | k1_xboole_0 = k2_xboole_0(k1_tarski(k4_tarski(X5,X4)),k1_xboole_0)) )),
% 1.85/0.61    inference(resolution,[],[f109,f56])).
% 1.85/0.61  fof(f56,plain,(
% 1.85/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 1.85/0.61    inference(cnf_transformation,[],[f20])).
% 1.85/0.61  fof(f20,plain,(
% 1.85/0.61    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 1.85/0.61    inference(ennf_transformation,[],[f4])).
% 1.85/0.61  fof(f4,axiom,(
% 1.85/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.85/0.61  fof(f109,plain,(
% 1.85/0.61    ( ! [X12,X11] : (r2_hidden(k4_tarski(X12,X11),k1_xboole_0) | ~r2_hidden(X11,k11_relat_1(k1_xboole_0,X12))) )),
% 1.85/0.61    inference(resolution,[],[f99,f68])).
% 1.85/0.61  fof(f68,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f40])).
% 1.85/0.61  fof(f99,plain,(
% 1.85/0.61    v1_relat_1(k1_xboole_0)),
% 1.85/0.61    inference(superposition,[],[f81,f51])).
% 1.85/0.61  fof(f51,plain,(
% 1.85/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f2])).
% 1.85/0.61  fof(f2,axiom,(
% 1.85/0.61    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.85/0.61  fof(f81,plain,(
% 1.85/0.61    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK1,X0))) )),
% 1.85/0.61    inference(unit_resulting_resolution,[],[f46,f54])).
% 1.85/0.61  fof(f54,plain,(
% 1.85/0.61    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f17])).
% 1.85/0.61  fof(f17,plain,(
% 1.85/0.61    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.85/0.61    inference(ennf_transformation,[],[f8])).
% 1.85/0.61  fof(f8,axiom,(
% 1.85/0.61    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 1.85/0.61  fof(f46,plain,(
% 1.85/0.61    v1_relat_1(sK1)),
% 1.85/0.61    inference(cnf_transformation,[],[f26])).
% 1.85/0.61  fof(f26,plain,(
% 1.85/0.61    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 1.85/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).
% 1.85/0.61  fof(f25,plain,(
% 1.85/0.61    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 1.85/0.61    introduced(choice_axiom,[])).
% 1.85/0.61  fof(f24,plain,(
% 1.85/0.61    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.85/0.61    inference(flattening,[],[f23])).
% 1.85/0.61  fof(f23,plain,(
% 1.85/0.61    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 1.85/0.61    inference(nnf_transformation,[],[f15])).
% 1.85/0.61  fof(f15,plain,(
% 1.85/0.61    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.85/0.61    inference(ennf_transformation,[],[f14])).
% 1.85/0.61  fof(f14,negated_conjecture,(
% 1.85/0.61    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.85/0.61    inference(negated_conjecture,[],[f13])).
% 1.85/0.61  fof(f13,conjecture,(
% 1.85/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 1.85/0.61  fof(f856,plain,(
% 1.85/0.61    r2_hidden(sK5(sK1,sK0),k1_xboole_0)),
% 1.85/0.61    inference(forward_demodulation,[],[f843,f809])).
% 1.85/0.61  fof(f809,plain,(
% 1.85/0.61    k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.85/0.61    inference(duplicate_literal_removal,[],[f803])).
% 1.85/0.61  fof(f803,plain,(
% 1.85/0.61    k1_xboole_0 = k11_relat_1(sK1,sK0) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.85/0.61    inference(resolution,[],[f614,f48])).
% 1.85/0.61  fof(f48,plain,(
% 1.85/0.61    ~r2_hidden(sK0,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.85/0.61    inference(cnf_transformation,[],[f26])).
% 1.85/0.61  fof(f614,plain,(
% 1.85/0.61    ( ! [X8] : (r2_hidden(X8,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,X8)) )),
% 1.85/0.61    inference(resolution,[],[f277,f188])).
% 1.85/0.61  fof(f188,plain,(
% 1.85/0.61    ( ! [X4,X5] : (~r2_hidden(X4,k11_relat_1(sK1,X5)) | r2_hidden(X5,k1_relat_1(sK1))) )),
% 1.85/0.61    inference(resolution,[],[f88,f75])).
% 1.85/0.61  fof(f75,plain,(
% 1.85/0.61    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 1.85/0.61    inference(equality_resolution,[],[f58])).
% 1.85/0.61  fof(f58,plain,(
% 1.85/0.61    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.85/0.61    inference(cnf_transformation,[],[f34])).
% 1.85/0.61  fof(f88,plain,(
% 1.85/0.61    ( ! [X12,X11] : (r2_hidden(k4_tarski(X12,X11),sK1) | ~r2_hidden(X11,k11_relat_1(sK1,X12))) )),
% 1.85/0.61    inference(resolution,[],[f46,f68])).
% 1.85/0.61  fof(f277,plain,(
% 1.85/0.61    ( ! [X3] : (r2_hidden(sK3(k1_xboole_0,X3),X3) | k1_xboole_0 = X3) )),
% 1.85/0.61    inference(forward_demodulation,[],[f276,f246])).
% 1.85/0.61  fof(f246,plain,(
% 1.85/0.61    ( ! [X0] : (k1_xboole_0 = k11_relat_1(k1_xboole_0,X0)) )),
% 1.85/0.61    inference(forward_demodulation,[],[f236,f49])).
% 1.85/0.61  fof(f236,plain,(
% 1.85/0.61    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k11_relat_1(k1_xboole_0,X0)) )),
% 1.85/0.61    inference(unit_resulting_resolution,[],[f208,f210,f59])).
% 1.85/0.61  fof(f59,plain,(
% 1.85/0.61    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | k1_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),X1)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f34])).
% 1.85/0.61  fof(f276,plain,(
% 1.85/0.61    ( ! [X2,X3] : (k1_xboole_0 = X3 | r2_hidden(sK3(k11_relat_1(k1_xboole_0,X2),X3),X3)) )),
% 1.85/0.61    inference(forward_demodulation,[],[f265,f49])).
% 1.85/0.61  fof(f265,plain,(
% 1.85/0.61    ( ! [X2,X3] : (k1_relat_1(k1_xboole_0) = X3 | r2_hidden(sK3(k11_relat_1(k1_xboole_0,X2),X3),X3)) )),
% 1.85/0.61    inference(backward_demodulation,[],[f228,f246])).
% 1.85/0.61  fof(f228,plain,(
% 1.85/0.61    ( ! [X2,X3] : (k1_relat_1(k11_relat_1(k1_xboole_0,X2)) = X3 | r2_hidden(sK3(k11_relat_1(k1_xboole_0,X2),X3),X3)) )),
% 1.85/0.61    inference(resolution,[],[f208,f59])).
% 1.85/0.61  fof(f843,plain,(
% 1.85/0.61    r2_hidden(sK5(sK1,sK0),k11_relat_1(sK1,sK0))),
% 1.85/0.61    inference(unit_resulting_resolution,[],[f46,f812,f67])).
% 1.85/0.61  fof(f812,plain,(
% 1.85/0.61    r2_hidden(k4_tarski(sK0,sK5(sK1,sK0)),sK1)),
% 1.85/0.61    inference(unit_resulting_resolution,[],[f811,f76])).
% 1.85/0.61  fof(f811,plain,(
% 1.85/0.61    r2_hidden(sK0,k1_relat_1(sK1))),
% 1.85/0.61    inference(trivial_inequality_removal,[],[f810])).
% 1.85/0.61  fof(f810,plain,(
% 1.85/0.61    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK0,k1_relat_1(sK1))),
% 1.85/0.61    inference(backward_demodulation,[],[f47,f809])).
% 1.85/0.61  fof(f47,plain,(
% 1.85/0.61    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 1.85/0.61    inference(cnf_transformation,[],[f26])).
% 1.85/0.61  % SZS output end Proof for theBenchmark
% 1.85/0.61  % (6920)------------------------------
% 1.85/0.61  % (6920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.61  % (6920)Termination reason: Refutation
% 1.85/0.61  
% 1.85/0.61  % (6920)Memory used [KB]: 6780
% 1.85/0.61  % (6920)Time elapsed: 0.122 s
% 1.85/0.61  % (6920)------------------------------
% 1.85/0.61  % (6920)------------------------------
% 1.85/0.61  % (6904)Success in time 0.246 s
%------------------------------------------------------------------------------

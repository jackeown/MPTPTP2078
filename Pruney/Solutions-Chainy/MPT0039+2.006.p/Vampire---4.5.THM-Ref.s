%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 403 expanded)
%              Number of leaves         :    6 (  98 expanded)
%              Depth                    :   18
%              Number of atoms          :  174 (2786 expanded)
%              Number of equality atoms :   51 ( 545 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f713,plain,(
    $false ),
    inference(subsumption_resolution,[],[f712,f17])).

fof(f17,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( sK0 != sK1
    & k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) )
   => ( sK0 != sK1
      & k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f712,plain,(
    sK0 = sK1 ),
    inference(backward_demodulation,[],[f444,f699])).

fof(f699,plain,(
    sK0 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f43,f698])).

fof(f698,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK1,X1,sK0),X1)
      | sK0 = k4_xboole_0(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f696,f120])).

fof(f120,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,X0,sK0),sK0)
      | sK0 = k4_xboole_0(sK1,X0) ) ),
    inference(factoring,[],[f70])).

fof(f70,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(sK1,X2,X3),sK0)
      | r2_hidden(sK3(sK1,X2,X3),X3)
      | k4_xboole_0(sK1,X2) = X3 ) ),
    inference(resolution,[],[f32,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f11])).

% (1050)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f32,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | r2_hidden(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f30,f31])).

fof(f31,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f28,f26])).

fof(f26,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK0,sK1))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f27,f16])).

fof(f16,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X2] :
      ( r2_hidden(X2,k4_xboole_0(sK0,sK1))
      | r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(superposition,[],[f25,f16])).

fof(f25,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f696,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK1,X1,sK0),X1)
      | sK0 = k4_xboole_0(sK1,X1)
      | ~ r2_hidden(sK3(sK1,X1,sK0),sK0) ) ),
    inference(resolution,[],[f146,f40])).

fof(f40,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK1)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(resolution,[],[f31,f25])).

fof(f146,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK1,X0,sK0),sK1)
      | r2_hidden(sK3(sK1,X0,sK0),X0)
      | sK0 = k4_xboole_0(sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,(
    ! [X0] :
      ( sK0 = k4_xboole_0(sK1,X0)
      | r2_hidden(sK3(sK1,X0,sK0),X0)
      | ~ r2_hidden(sK3(sK1,X0,sK0),sK1)
      | sK0 = k4_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f120,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f31,f33])).

fof(f33,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f31,f18])).

fof(f18,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f6,f9])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f444,plain,(
    sK1 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f43,f321])).

fof(f321,plain,(
    ! [X7] :
      ( r2_hidden(sK3(sK1,X7,sK1),X7)
      | sK1 = k4_xboole_0(sK1,X7) ) ),
    inference(subsumption_resolution,[],[f317,f22])).

fof(f317,plain,(
    ! [X7] :
      ( r2_hidden(sK3(sK1,X7,sK1),X7)
      | ~ r2_hidden(sK3(sK1,X7,sK1),sK1)
      | sK1 = k4_xboole_0(sK1,X7) ) ),
    inference(duplicate_literal_removal,[],[f314])).

fof(f314,plain,(
    ! [X7] :
      ( r2_hidden(sK3(sK1,X7,sK1),X7)
      | ~ r2_hidden(sK3(sK1,X7,sK1),sK1)
      | sK1 = k4_xboole_0(sK1,X7)
      | sK1 = k4_xboole_0(sK1,X7) ) ),
    inference(resolution,[],[f71,f100])).

fof(f100,plain,(
    ! [X9] :
      ( r2_hidden(sK3(sK1,X9,sK1),sK0)
      | sK1 = k4_xboole_0(sK1,X9) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X9] :
      ( r2_hidden(sK3(sK1,X9,sK1),sK0)
      | sK1 = k4_xboole_0(sK1,X9)
      | r2_hidden(sK3(sK1,X9,sK1),sK0) ) ),
    inference(resolution,[],[f69,f32])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,sK1),sK0)
      | r2_hidden(sK3(X0,X1,sK1),X0)
      | k4_xboole_0(X0,X1) = sK1 ) ),
    inference(resolution,[],[f32,f22])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,sK1),sK0)
      | r2_hidden(sK3(X0,X1,sK1),X1)
      | ~ r2_hidden(sK3(X0,X1,sK1),X0)
      | k4_xboole_0(X0,X1) = sK1 ) ),
    inference(resolution,[],[f40,f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:17:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (1056)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.46  % (1049)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (1064)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (1067)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (1051)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (1052)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (1058)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (1069)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (1063)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (1069)Refutation not found, incomplete strategy% (1069)------------------------------
% 0.21/0.50  % (1069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1069)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1069)Memory used [KB]: 10490
% 0.21/0.50  % (1069)Time elapsed: 0.079 s
% 0.21/0.50  % (1069)------------------------------
% 0.21/0.50  % (1069)------------------------------
% 0.21/0.50  % (1068)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (1064)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f713,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f712,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    sK0 != sK1),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    sK0 != sK1 & k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0,X1] : (X0 != X1 & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)) => (sK0 != sK1 & k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f5,plain,(
% 0.21/0.50    ? [X0,X1] : (X0 != X1 & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 0.21/0.50    inference(negated_conjecture,[],[f3])).
% 0.21/0.50  fof(f3,conjecture,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 0.21/0.50  fof(f712,plain,(
% 0.21/0.50    sK0 = sK1),
% 0.21/0.50    inference(backward_demodulation,[],[f444,f699])).
% 0.21/0.50  fof(f699,plain,(
% 0.21/0.50    sK0 = k4_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f43,f698])).
% 0.21/0.50  fof(f698,plain,(
% 0.21/0.50    ( ! [X1] : (r2_hidden(sK3(sK1,X1,sK0),X1) | sK0 = k4_xboole_0(sK1,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f696,f120])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK3(sK1,X0,sK0),sK0) | sK0 = k4_xboole_0(sK1,X0)) )),
% 0.21/0.50    inference(factoring,[],[f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X3] : (r2_hidden(sK3(sK1,X2,X3),sK0) | r2_hidden(sK3(sK1,X2,X3),X3) | k4_xboole_0(sK1,X2) = X3) )),
% 0.21/0.50    inference(resolution,[],[f32,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(rectify,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  % (1050)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(X2,sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f30,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,sK1))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f28,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,sK1)) | r2_hidden(X0,sK1)) )),
% 0.21/0.50    inference(superposition,[],[f27,f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2] : (r2_hidden(X2,k4_xboole_0(sK0,sK1)) | r2_hidden(X2,sK0) | ~r2_hidden(X2,sK1)) )),
% 0.21/0.50    inference(superposition,[],[f25,f16])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f696,plain,(
% 0.21/0.50    ( ! [X1] : (r2_hidden(sK3(sK1,X1,sK0),X1) | sK0 = k4_xboole_0(sK1,X1) | ~r2_hidden(sK3(sK1,X1,sK0),sK0)) )),
% 0.21/0.50    inference(resolution,[],[f146,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X4] : (r2_hidden(X4,sK1) | ~r2_hidden(X4,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f31,f25])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK3(sK1,X0,sK0),sK1) | r2_hidden(sK3(sK1,X0,sK0),X0) | sK0 = k4_xboole_0(sK1,X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f143])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ( ! [X0] : (sK0 = k4_xboole_0(sK1,X0) | r2_hidden(sK3(sK1,X0,sK0),X0) | ~r2_hidden(sK3(sK1,X0,sK0),sK1) | sK0 = k4_xboole_0(sK1,X0)) )),
% 0.21/0.50    inference(resolution,[],[f120,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f31,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f31,f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f6,f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f6,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.50  fof(f444,plain,(
% 0.21/0.50    sK1 = k4_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f43,f321])).
% 0.21/0.50  fof(f321,plain,(
% 0.21/0.50    ( ! [X7] : (r2_hidden(sK3(sK1,X7,sK1),X7) | sK1 = k4_xboole_0(sK1,X7)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f317,f22])).
% 0.21/0.50  fof(f317,plain,(
% 0.21/0.50    ( ! [X7] : (r2_hidden(sK3(sK1,X7,sK1),X7) | ~r2_hidden(sK3(sK1,X7,sK1),sK1) | sK1 = k4_xboole_0(sK1,X7)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f314])).
% 0.21/0.50  fof(f314,plain,(
% 0.21/0.50    ( ! [X7] : (r2_hidden(sK3(sK1,X7,sK1),X7) | ~r2_hidden(sK3(sK1,X7,sK1),sK1) | sK1 = k4_xboole_0(sK1,X7) | sK1 = k4_xboole_0(sK1,X7)) )),
% 0.21/0.50    inference(resolution,[],[f71,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ( ! [X9] : (r2_hidden(sK3(sK1,X9,sK1),sK0) | sK1 = k4_xboole_0(sK1,X9)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ( ! [X9] : (r2_hidden(sK3(sK1,X9,sK1),sK0) | sK1 = k4_xboole_0(sK1,X9) | r2_hidden(sK3(sK1,X9,sK1),sK0)) )),
% 0.21/0.50    inference(resolution,[],[f69,f32])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,sK1),sK0) | r2_hidden(sK3(X0,X1,sK1),X0) | k4_xboole_0(X0,X1) = sK1) )),
% 0.21/0.50    inference(resolution,[],[f32,f22])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1,sK1),sK0) | r2_hidden(sK3(X0,X1,sK1),X1) | ~r2_hidden(sK3(X0,X1,sK1),X0) | k4_xboole_0(X0,X1) = sK1) )),
% 0.21/0.50    inference(resolution,[],[f40,f24])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (1064)------------------------------
% 0.21/0.50  % (1064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1064)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (1064)Memory used [KB]: 6524
% 0.21/0.50  % (1064)Time elapsed: 0.082 s
% 0.21/0.50  % (1064)------------------------------
% 0.21/0.50  % (1064)------------------------------
% 0.21/0.50  % (1055)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (1048)Success in time 0.145 s
%------------------------------------------------------------------------------

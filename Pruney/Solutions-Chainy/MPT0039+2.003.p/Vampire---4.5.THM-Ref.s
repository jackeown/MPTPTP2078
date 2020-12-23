%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:47 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 475 expanded)
%              Number of leaves         :    4 ( 114 expanded)
%              Depth                    :   18
%              Number of atoms          :  174 (3420 expanded)
%              Number of equality atoms :   52 ( 651 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1285,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1284,f14])).

fof(f14,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,
    ( sK0 != sK1
    & k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).

fof(f6,plain,
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

fof(f1284,plain,(
    sK0 = sK1 ),
    inference(backward_demodulation,[],[f1123,f1277])).

fof(f1277,plain,(
    ! [X5] : sK0 = k4_xboole_0(sK1,k4_xboole_0(X5,X5)) ),
    inference(resolution,[],[f1271,f49])).

fof(f49,plain,(
    ! [X4,X3] : ~ r2_hidden(X4,k4_xboole_0(X3,X3)) ),
    inference(superposition,[],[f27,f45])).

fof(f45,plain,(
    ! [X1] : k4_xboole_0(sK0,sK1) = k4_xboole_0(X1,X1) ),
    inference(subsumption_resolution,[],[f43,f27])).

fof(f43,plain,(
    ! [X1] :
      ( k4_xboole_0(sK0,sK1) = k4_xboole_0(X1,X1)
      | r2_hidden(sK2(X1,X1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f38])).

fof(f38,plain,(
    ! [X1] :
      ( k4_xboole_0(sK0,sK1) = k4_xboole_0(X1,X1)
      | k4_xboole_0(sK0,sK1) = k4_xboole_0(X1,X1)
      | r2_hidden(sK2(X1,X1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f29,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f11])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
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
    inference(rectify,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,k4_xboole_0(sK0,sK1)),X0)
      | k4_xboole_0(X0,X1) = k4_xboole_0(sK0,sK1) ) ),
    inference(resolution,[],[f27,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f24,f22])).

fof(f22,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK0,sK1))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f23,f13])).

fof(f13,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1271,plain,(
    ! [X1] :
      ( r2_hidden(sK2(sK1,X1,sK0),X1)
      | sK0 = k4_xboole_0(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f1269,f239])).

fof(f239,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0,sK0),sK0)
      | sK0 = k4_xboole_0(sK1,X0) ) ),
    inference(factoring,[],[f33])).

fof(f33,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK2(sK1,X2,X3),sK0)
      | r2_hidden(sK2(sK1,X2,X3),X3)
      | k4_xboole_0(sK1,X2) = X3 ) ),
    inference(resolution,[],[f28,f18])).

fof(f28,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | r2_hidden(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f26,f27])).

fof(f26,plain,(
    ! [X2] :
      ( r2_hidden(X2,k4_xboole_0(sK0,sK1))
      | r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(superposition,[],[f21,f13])).

fof(f21,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1269,plain,(
    ! [X1] :
      ( r2_hidden(sK2(sK1,X1,sK0),X1)
      | sK0 = k4_xboole_0(sK1,X1)
      | ~ r2_hidden(sK2(sK1,X1,sK0),sK0) ) ),
    inference(resolution,[],[f306,f31])).

fof(f31,plain,(
    ! [X4] :
      ( r2_hidden(X4,sK1)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(resolution,[],[f27,f21])).

fof(f306,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(sK1,X0,sK0),sK1)
      | r2_hidden(sK2(sK1,X0,sK0),X0)
      | sK0 = k4_xboole_0(sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f303])).

fof(f303,plain,(
    ! [X0] :
      ( sK0 = k4_xboole_0(sK1,X0)
      | r2_hidden(sK2(sK1,X0,sK0),X0)
      | ~ r2_hidden(sK2(sK1,X0,sK0),sK1)
      | sK0 = k4_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f239,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1123,plain,(
    ! [X5] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X5,X5)) ),
    inference(resolution,[],[f670,f49])).

fof(f670,plain,(
    ! [X7] :
      ( r2_hidden(sK2(sK1,X7,sK1),X7)
      | sK1 = k4_xboole_0(sK1,X7) ) ),
    inference(subsumption_resolution,[],[f666,f18])).

fof(f666,plain,(
    ! [X7] :
      ( r2_hidden(sK2(sK1,X7,sK1),X7)
      | ~ r2_hidden(sK2(sK1,X7,sK1),sK1)
      | sK1 = k4_xboole_0(sK1,X7) ) ),
    inference(duplicate_literal_removal,[],[f658])).

fof(f658,plain,(
    ! [X7] :
      ( r2_hidden(sK2(sK1,X7,sK1),X7)
      | ~ r2_hidden(sK2(sK1,X7,sK1),sK1)
      | sK1 = k4_xboole_0(sK1,X7)
      | sK1 = k4_xboole_0(sK1,X7) ) ),
    inference(resolution,[],[f34,f220])).

fof(f220,plain,(
    ! [X11] :
      ( r2_hidden(sK2(sK1,X11,sK1),sK0)
      | sK1 = k4_xboole_0(sK1,X11) ) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,(
    ! [X11] :
      ( r2_hidden(sK2(sK1,X11,sK1),sK0)
      | sK1 = k4_xboole_0(sK1,X11)
      | r2_hidden(sK2(sK1,X11,sK1),sK0) ) ),
    inference(resolution,[],[f32,f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,sK1),sK0)
      | r2_hidden(sK2(X0,X1,sK1),X0)
      | k4_xboole_0(X0,X1) = sK1 ) ),
    inference(resolution,[],[f28,f18])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,sK1),sK0)
      | r2_hidden(sK2(X0,X1,sK1),X1)
      | ~ r2_hidden(sK2(X0,X1,sK1),X0)
      | k4_xboole_0(X0,X1) = sK1 ) ),
    inference(resolution,[],[f31,f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:57:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (15723)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (15726)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (15721)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (15730)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (15731)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (15722)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (15724)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (15743)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (15739)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (15735)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (15725)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (15734)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (15742)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (15730)Refutation not found, incomplete strategy% (15730)------------------------------
% 0.21/0.52  % (15730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15730)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15730)Memory used [KB]: 10618
% 0.21/0.52  % (15730)Time elapsed: 0.096 s
% 0.21/0.52  % (15730)------------------------------
% 0.21/0.52  % (15730)------------------------------
% 0.21/0.52  % (15735)Refutation not found, incomplete strategy% (15735)------------------------------
% 0.21/0.52  % (15735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15735)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15735)Memory used [KB]: 6140
% 0.21/0.52  % (15735)Time elapsed: 0.003 s
% 0.21/0.52  % (15735)------------------------------
% 0.21/0.52  % (15735)------------------------------
% 0.21/0.52  % (15736)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (15732)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (15737)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (15737)Refutation not found, incomplete strategy% (15737)------------------------------
% 0.21/0.53  % (15737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15737)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15737)Memory used [KB]: 10618
% 0.21/0.53  % (15737)Time elapsed: 0.123 s
% 0.21/0.53  % (15737)------------------------------
% 0.21/0.53  % (15737)------------------------------
% 0.21/0.53  % (15748)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (15749)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (15720)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (15745)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (15747)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (15729)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (15744)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (15740)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (15733)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (15746)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (15728)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (15740)Refutation not found, incomplete strategy% (15740)------------------------------
% 0.21/0.55  % (15740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15740)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15740)Memory used [KB]: 10618
% 0.21/0.55  % (15740)Time elapsed: 0.149 s
% 0.21/0.55  % (15740)------------------------------
% 0.21/0.55  % (15740)------------------------------
% 0.21/0.55  % (15741)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (15727)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.64/0.57  % (15738)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.77/0.61  % (15728)Refutation found. Thanks to Tanya!
% 1.77/0.61  % SZS status Theorem for theBenchmark
% 1.77/0.61  % SZS output start Proof for theBenchmark
% 1.77/0.61  fof(f1285,plain,(
% 1.77/0.61    $false),
% 1.77/0.61    inference(subsumption_resolution,[],[f1284,f14])).
% 1.77/0.61  fof(f14,plain,(
% 1.77/0.61    sK0 != sK1),
% 1.77/0.61    inference(cnf_transformation,[],[f7])).
% 1.77/0.61  fof(f7,plain,(
% 1.77/0.61    sK0 != sK1 & k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0)),
% 1.77/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).
% 1.77/0.61  fof(f6,plain,(
% 1.77/0.61    ? [X0,X1] : (X0 != X1 & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)) => (sK0 != sK1 & k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0))),
% 1.77/0.61    introduced(choice_axiom,[])).
% 1.77/0.61  fof(f5,plain,(
% 1.77/0.61    ? [X0,X1] : (X0 != X1 & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0))),
% 1.77/0.61    inference(ennf_transformation,[],[f4])).
% 1.77/0.61  fof(f4,negated_conjecture,(
% 1.77/0.61    ~! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 1.77/0.61    inference(negated_conjecture,[],[f3])).
% 1.77/0.61  fof(f3,conjecture,(
% 1.77/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 1.77/0.61  fof(f1284,plain,(
% 1.77/0.61    sK0 = sK1),
% 1.77/0.61    inference(backward_demodulation,[],[f1123,f1277])).
% 1.77/0.61  fof(f1277,plain,(
% 1.77/0.61    ( ! [X5] : (sK0 = k4_xboole_0(sK1,k4_xboole_0(X5,X5))) )),
% 1.77/0.61    inference(resolution,[],[f1271,f49])).
% 1.77/0.61  fof(f49,plain,(
% 1.77/0.61    ( ! [X4,X3] : (~r2_hidden(X4,k4_xboole_0(X3,X3))) )),
% 1.77/0.61    inference(superposition,[],[f27,f45])).
% 1.77/0.61  fof(f45,plain,(
% 1.77/0.61    ( ! [X1] : (k4_xboole_0(sK0,sK1) = k4_xboole_0(X1,X1)) )),
% 1.77/0.61    inference(subsumption_resolution,[],[f43,f27])).
% 1.77/0.61  fof(f43,plain,(
% 1.77/0.61    ( ! [X1] : (k4_xboole_0(sK0,sK1) = k4_xboole_0(X1,X1) | r2_hidden(sK2(X1,X1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))) )),
% 1.77/0.61    inference(duplicate_literal_removal,[],[f38])).
% 1.77/0.61  fof(f38,plain,(
% 1.77/0.61    ( ! [X1] : (k4_xboole_0(sK0,sK1) = k4_xboole_0(X1,X1) | k4_xboole_0(sK0,sK1) = k4_xboole_0(X1,X1) | r2_hidden(sK2(X1,X1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))) )),
% 1.77/0.61    inference(resolution,[],[f29,f19])).
% 1.77/0.61  fof(f19,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f12])).
% 1.77/0.61  fof(f12,plain,(
% 1.77/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.77/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f11])).
% 1.77/0.61  fof(f11,plain,(
% 1.77/0.61    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.77/0.61    introduced(choice_axiom,[])).
% 1.77/0.61  fof(f10,plain,(
% 1.77/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.77/0.61    inference(rectify,[],[f9])).
% 1.77/0.61  fof(f9,plain,(
% 1.77/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.77/0.61    inference(flattening,[],[f8])).
% 1.77/0.61  fof(f8,plain,(
% 1.77/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.77/0.61    inference(nnf_transformation,[],[f2])).
% 1.77/0.61  fof(f2,axiom,(
% 1.77/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.77/0.61  fof(f29,plain,(
% 1.77/0.61    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,k4_xboole_0(sK0,sK1)),X0) | k4_xboole_0(X0,X1) = k4_xboole_0(sK0,sK1)) )),
% 1.77/0.61    inference(resolution,[],[f27,f18])).
% 1.77/0.61  fof(f18,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 1.77/0.61    inference(cnf_transformation,[],[f12])).
% 1.77/0.61  fof(f27,plain,(
% 1.77/0.61    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,sK1))) )),
% 1.77/0.61    inference(subsumption_resolution,[],[f24,f22])).
% 1.77/0.61  fof(f22,plain,(
% 1.77/0.61    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.77/0.61    inference(equality_resolution,[],[f16])).
% 1.77/0.61  fof(f16,plain,(
% 1.77/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.77/0.61    inference(cnf_transformation,[],[f12])).
% 1.77/0.61  fof(f24,plain,(
% 1.77/0.61    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,sK1)) | r2_hidden(X0,sK1)) )),
% 1.77/0.61    inference(superposition,[],[f23,f13])).
% 1.77/0.61  fof(f13,plain,(
% 1.77/0.61    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0)),
% 1.77/0.61    inference(cnf_transformation,[],[f7])).
% 1.77/0.61  fof(f23,plain,(
% 1.77/0.61    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.77/0.61    inference(equality_resolution,[],[f15])).
% 1.77/0.61  fof(f15,plain,(
% 1.77/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.77/0.61    inference(cnf_transformation,[],[f12])).
% 1.77/0.61  fof(f1271,plain,(
% 1.77/0.61    ( ! [X1] : (r2_hidden(sK2(sK1,X1,sK0),X1) | sK0 = k4_xboole_0(sK1,X1)) )),
% 1.77/0.61    inference(subsumption_resolution,[],[f1269,f239])).
% 1.77/0.61  fof(f239,plain,(
% 1.77/0.61    ( ! [X0] : (r2_hidden(sK2(sK1,X0,sK0),sK0) | sK0 = k4_xboole_0(sK1,X0)) )),
% 1.77/0.61    inference(factoring,[],[f33])).
% 1.77/0.61  fof(f33,plain,(
% 1.77/0.61    ( ! [X2,X3] : (r2_hidden(sK2(sK1,X2,X3),sK0) | r2_hidden(sK2(sK1,X2,X3),X3) | k4_xboole_0(sK1,X2) = X3) )),
% 1.77/0.61    inference(resolution,[],[f28,f18])).
% 1.77/0.61  fof(f28,plain,(
% 1.77/0.61    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(X2,sK0)) )),
% 1.77/0.61    inference(subsumption_resolution,[],[f26,f27])).
% 1.77/0.61  fof(f26,plain,(
% 1.77/0.61    ( ! [X2] : (r2_hidden(X2,k4_xboole_0(sK0,sK1)) | r2_hidden(X2,sK0) | ~r2_hidden(X2,sK1)) )),
% 1.77/0.61    inference(superposition,[],[f21,f13])).
% 1.77/0.61  fof(f21,plain,(
% 1.77/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.77/0.61    inference(equality_resolution,[],[f17])).
% 1.77/0.61  fof(f17,plain,(
% 1.77/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.77/0.61    inference(cnf_transformation,[],[f12])).
% 1.77/0.61  fof(f1269,plain,(
% 1.77/0.61    ( ! [X1] : (r2_hidden(sK2(sK1,X1,sK0),X1) | sK0 = k4_xboole_0(sK1,X1) | ~r2_hidden(sK2(sK1,X1,sK0),sK0)) )),
% 1.77/0.61    inference(resolution,[],[f306,f31])).
% 1.77/0.61  fof(f31,plain,(
% 1.77/0.61    ( ! [X4] : (r2_hidden(X4,sK1) | ~r2_hidden(X4,sK0)) )),
% 1.77/0.61    inference(resolution,[],[f27,f21])).
% 1.77/0.61  fof(f306,plain,(
% 1.77/0.61    ( ! [X0] : (~r2_hidden(sK2(sK1,X0,sK0),sK1) | r2_hidden(sK2(sK1,X0,sK0),X0) | sK0 = k4_xboole_0(sK1,X0)) )),
% 1.77/0.61    inference(duplicate_literal_removal,[],[f303])).
% 1.77/0.61  fof(f303,plain,(
% 1.77/0.61    ( ! [X0] : (sK0 = k4_xboole_0(sK1,X0) | r2_hidden(sK2(sK1,X0,sK0),X0) | ~r2_hidden(sK2(sK1,X0,sK0),sK1) | sK0 = k4_xboole_0(sK1,X0)) )),
% 1.77/0.61    inference(resolution,[],[f239,f20])).
% 1.77/0.61  fof(f20,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 1.77/0.61    inference(cnf_transformation,[],[f12])).
% 1.77/0.61  fof(f1123,plain,(
% 1.77/0.61    ( ! [X5] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(X5,X5))) )),
% 1.77/0.61    inference(resolution,[],[f670,f49])).
% 1.77/0.61  fof(f670,plain,(
% 1.77/0.61    ( ! [X7] : (r2_hidden(sK2(sK1,X7,sK1),X7) | sK1 = k4_xboole_0(sK1,X7)) )),
% 1.77/0.61    inference(subsumption_resolution,[],[f666,f18])).
% 1.77/0.61  fof(f666,plain,(
% 1.77/0.61    ( ! [X7] : (r2_hidden(sK2(sK1,X7,sK1),X7) | ~r2_hidden(sK2(sK1,X7,sK1),sK1) | sK1 = k4_xboole_0(sK1,X7)) )),
% 1.77/0.61    inference(duplicate_literal_removal,[],[f658])).
% 1.77/0.61  fof(f658,plain,(
% 1.77/0.61    ( ! [X7] : (r2_hidden(sK2(sK1,X7,sK1),X7) | ~r2_hidden(sK2(sK1,X7,sK1),sK1) | sK1 = k4_xboole_0(sK1,X7) | sK1 = k4_xboole_0(sK1,X7)) )),
% 1.77/0.61    inference(resolution,[],[f34,f220])).
% 1.77/0.61  fof(f220,plain,(
% 1.77/0.61    ( ! [X11] : (r2_hidden(sK2(sK1,X11,sK1),sK0) | sK1 = k4_xboole_0(sK1,X11)) )),
% 1.77/0.61    inference(duplicate_literal_removal,[],[f218])).
% 1.77/0.61  fof(f218,plain,(
% 1.77/0.61    ( ! [X11] : (r2_hidden(sK2(sK1,X11,sK1),sK0) | sK1 = k4_xboole_0(sK1,X11) | r2_hidden(sK2(sK1,X11,sK1),sK0)) )),
% 1.77/0.61    inference(resolution,[],[f32,f28])).
% 1.77/0.61  fof(f32,plain,(
% 1.77/0.61    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,sK1),sK0) | r2_hidden(sK2(X0,X1,sK1),X0) | k4_xboole_0(X0,X1) = sK1) )),
% 1.77/0.61    inference(resolution,[],[f28,f18])).
% 1.77/0.61  fof(f34,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1,sK1),sK0) | r2_hidden(sK2(X0,X1,sK1),X1) | ~r2_hidden(sK2(X0,X1,sK1),X0) | k4_xboole_0(X0,X1) = sK1) )),
% 1.77/0.61    inference(resolution,[],[f31,f20])).
% 1.77/0.61  % SZS output end Proof for theBenchmark
% 1.77/0.61  % (15728)------------------------------
% 1.77/0.61  % (15728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.61  % (15728)Termination reason: Refutation
% 1.77/0.61  
% 1.77/0.61  % (15728)Memory used [KB]: 11257
% 1.77/0.61  % (15728)Time elapsed: 0.206 s
% 1.77/0.61  % (15728)------------------------------
% 1.77/0.61  % (15728)------------------------------
% 1.77/0.61  % (15719)Success in time 0.256 s
%------------------------------------------------------------------------------

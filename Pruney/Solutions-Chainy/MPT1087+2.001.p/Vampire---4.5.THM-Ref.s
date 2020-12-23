%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:23 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 102 expanded)
%              Number of leaves         :    5 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  127 ( 516 expanded)
%              Number of equality atoms :   17 (  55 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f246,plain,(
    $false ),
    inference(subsumption_resolution,[],[f230,f18])).

fof(f18,plain,(
    ~ v1_finset_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ v1_finset_1(k3_xboole_0(sK0,sK1))
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k3_xboole_0(X0,X1))
        & v1_finset_1(X0) )
   => ( ~ v1_finset_1(k3_xboole_0(sK0,sK1))
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k3_xboole_0(X0,X1))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_finset_1(X0)
       => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_finset_1)).

fof(f230,plain,(
    v1_finset_1(k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f32,f216])).

fof(f216,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f215,f18])).

fof(f215,plain,(
    ! [X0] :
      ( v1_finset_1(k3_xboole_0(sK0,X0))
      | k3_xboole_0(sK0,X0) = k3_xboole_0(k3_xboole_0(sK0,X0),sK0) ) ),
    inference(duplicate_literal_removal,[],[f205])).

fof(f205,plain,(
    ! [X0] :
      ( v1_finset_1(k3_xboole_0(sK0,X0))
      | k3_xboole_0(sK0,X0) = k3_xboole_0(k3_xboole_0(sK0,X0),sK0)
      | v1_finset_1(k3_xboole_0(sK0,X0)) ) ),
    inference(resolution,[],[f152,f155])).

fof(f155,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0,sK0,X0),sK0)
      | k3_xboole_0(X0,sK0) = X0
      | v1_finset_1(X0) ) ),
    inference(subsumption_resolution,[],[f148,f146])).

fof(f146,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0,sK0,X0),X0)
      | v1_finset_1(X0) ) ),
    inference(factoring,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,sK0,X1),X1)
      | r2_hidden(sK2(X0,sK0,X1),X0)
      | v1_finset_1(X1) ) ),
    inference(superposition,[],[f32,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f15])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f148,plain,(
    ! [X0] :
      ( v1_finset_1(X0)
      | k3_xboole_0(X0,sK0) = X0
      | ~ r2_hidden(sK2(X0,sK0,X0),sK0)
      | ~ r2_hidden(sK2(X0,sK0,X0),X0) ) ),
    inference(resolution,[],[f146,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f152,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK2(k3_xboole_0(X6,X7),sK0,k3_xboole_0(X6,X7)),X6)
      | v1_finset_1(k3_xboole_0(X6,X7)) ) ),
    inference(resolution,[],[f146,f31])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0] : v1_finset_1(k3_xboole_0(X0,sK0)) ),
    inference(resolution,[],[f17,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_finset_1)).

fof(f17,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : run_vampire %s %d
% 0.10/0.30  % Computer   : n017.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 09:50:31 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.16/0.41  % (31737)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.16/0.41  % (31749)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.16/0.41  % (31751)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.16/0.42  % (31760)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.16/0.42  % (31752)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.16/0.43  % (31742)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.16/0.43  % (31742)Refutation not found, incomplete strategy% (31742)------------------------------
% 0.16/0.43  % (31742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.43  % (31742)Termination reason: Refutation not found, incomplete strategy
% 0.16/0.43  
% 0.16/0.43  % (31742)Memory used [KB]: 6140
% 0.16/0.43  % (31742)Time elapsed: 0.086 s
% 0.16/0.43  % (31742)------------------------------
% 0.16/0.43  % (31742)------------------------------
% 0.16/0.43  % (31762)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.16/0.44  % (31754)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.16/0.44  % (31754)Refutation not found, incomplete strategy% (31754)------------------------------
% 0.16/0.44  % (31754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.44  % (31754)Termination reason: Refutation not found, incomplete strategy
% 0.16/0.44  
% 0.16/0.44  % (31754)Memory used [KB]: 10618
% 0.16/0.44  % (31754)Time elapsed: 0.096 s
% 0.16/0.44  % (31754)------------------------------
% 0.16/0.44  % (31754)------------------------------
% 0.16/0.44  % (31743)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.16/0.45  % (31763)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.16/0.45  % (31760)Refutation found. Thanks to Tanya!
% 0.16/0.45  % SZS status Theorem for theBenchmark
% 0.16/0.45  % SZS output start Proof for theBenchmark
% 0.16/0.45  fof(f246,plain,(
% 0.16/0.45    $false),
% 0.16/0.45    inference(subsumption_resolution,[],[f230,f18])).
% 0.16/0.45  fof(f18,plain,(
% 0.16/0.45    ~v1_finset_1(k3_xboole_0(sK0,sK1))),
% 0.16/0.45    inference(cnf_transformation,[],[f11])).
% 0.16/0.45  fof(f11,plain,(
% 0.16/0.45    ~v1_finset_1(k3_xboole_0(sK0,sK1)) & v1_finset_1(sK0)),
% 0.16/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f10])).
% 0.16/0.45  fof(f10,plain,(
% 0.16/0.45    ? [X0,X1] : (~v1_finset_1(k3_xboole_0(X0,X1)) & v1_finset_1(X0)) => (~v1_finset_1(k3_xboole_0(sK0,sK1)) & v1_finset_1(sK0))),
% 0.16/0.45    introduced(choice_axiom,[])).
% 0.16/0.45  fof(f8,plain,(
% 0.16/0.45    ? [X0,X1] : (~v1_finset_1(k3_xboole_0(X0,X1)) & v1_finset_1(X0))),
% 0.16/0.45    inference(ennf_transformation,[],[f7])).
% 0.16/0.45  fof(f7,negated_conjecture,(
% 0.16/0.45    ~! [X0,X1] : (v1_finset_1(X0) => v1_finset_1(k3_xboole_0(X0,X1)))),
% 0.16/0.45    inference(negated_conjecture,[],[f6])).
% 0.16/0.45  fof(f6,conjecture,(
% 0.16/0.45    ! [X0,X1] : (v1_finset_1(X0) => v1_finset_1(k3_xboole_0(X0,X1)))),
% 0.16/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_finset_1)).
% 0.16/0.45  fof(f230,plain,(
% 0.16/0.45    v1_finset_1(k3_xboole_0(sK0,sK1))),
% 0.16/0.45    inference(superposition,[],[f32,f216])).
% 0.16/0.45  fof(f216,plain,(
% 0.16/0.45    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),sK0)),
% 0.16/0.45    inference(resolution,[],[f215,f18])).
% 0.16/0.45  fof(f215,plain,(
% 0.16/0.45    ( ! [X0] : (v1_finset_1(k3_xboole_0(sK0,X0)) | k3_xboole_0(sK0,X0) = k3_xboole_0(k3_xboole_0(sK0,X0),sK0)) )),
% 0.16/0.45    inference(duplicate_literal_removal,[],[f205])).
% 0.16/0.45  fof(f205,plain,(
% 0.16/0.45    ( ! [X0] : (v1_finset_1(k3_xboole_0(sK0,X0)) | k3_xboole_0(sK0,X0) = k3_xboole_0(k3_xboole_0(sK0,X0),sK0) | v1_finset_1(k3_xboole_0(sK0,X0))) )),
% 0.16/0.45    inference(resolution,[],[f152,f155])).
% 0.16/0.45  fof(f155,plain,(
% 0.16/0.45    ( ! [X0] : (~r2_hidden(sK2(X0,sK0,X0),sK0) | k3_xboole_0(X0,sK0) = X0 | v1_finset_1(X0)) )),
% 0.16/0.45    inference(subsumption_resolution,[],[f148,f146])).
% 0.16/0.45  fof(f146,plain,(
% 0.16/0.45    ( ! [X0] : (r2_hidden(sK2(X0,sK0,X0),X0) | v1_finset_1(X0)) )),
% 0.16/0.45    inference(factoring,[],[f38])).
% 0.16/0.45  fof(f38,plain,(
% 0.16/0.45    ( ! [X0,X1] : (r2_hidden(sK2(X0,sK0,X1),X1) | r2_hidden(sK2(X0,sK0,X1),X0) | v1_finset_1(X1)) )),
% 0.16/0.45    inference(superposition,[],[f32,f26])).
% 0.16/0.45  fof(f26,plain,(
% 0.16/0.45    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.16/0.45    inference(cnf_transformation,[],[f16])).
% 0.16/0.45  fof(f16,plain,(
% 0.16/0.45    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.16/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f15])).
% 0.16/0.45  fof(f15,plain,(
% 0.16/0.45    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.16/0.45    introduced(choice_axiom,[])).
% 0.16/0.45  fof(f14,plain,(
% 0.16/0.45    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.16/0.45    inference(rectify,[],[f13])).
% 0.16/0.45  fof(f13,plain,(
% 0.16/0.45    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.16/0.45    inference(flattening,[],[f12])).
% 0.16/0.45  fof(f12,plain,(
% 0.16/0.45    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.16/0.45    inference(nnf_transformation,[],[f1])).
% 0.16/0.45  fof(f1,axiom,(
% 0.16/0.45    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.16/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.16/0.45  fof(f148,plain,(
% 0.16/0.45    ( ! [X0] : (v1_finset_1(X0) | k3_xboole_0(X0,sK0) = X0 | ~r2_hidden(sK2(X0,sK0,X0),sK0) | ~r2_hidden(sK2(X0,sK0,X0),X0)) )),
% 0.16/0.45    inference(resolution,[],[f146,f28])).
% 0.16/0.45  fof(f28,plain,(
% 0.16/0.45    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.16/0.45    inference(cnf_transformation,[],[f16])).
% 0.16/0.45  fof(f152,plain,(
% 0.16/0.45    ( ! [X6,X7] : (r2_hidden(sK2(k3_xboole_0(X6,X7),sK0,k3_xboole_0(X6,X7)),X6) | v1_finset_1(k3_xboole_0(X6,X7))) )),
% 0.16/0.45    inference(resolution,[],[f146,f31])).
% 0.16/0.45  fof(f31,plain,(
% 0.16/0.45    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.16/0.45    inference(equality_resolution,[],[f23])).
% 0.16/0.45  fof(f23,plain,(
% 0.16/0.45    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.16/0.45    inference(cnf_transformation,[],[f16])).
% 0.16/0.45  fof(f32,plain,(
% 0.16/0.45    ( ! [X0] : (v1_finset_1(k3_xboole_0(X0,sK0))) )),
% 0.16/0.45    inference(resolution,[],[f17,f21])).
% 0.16/0.45  fof(f21,plain,(
% 0.16/0.45    ( ! [X0,X1] : (v1_finset_1(k3_xboole_0(X0,X1)) | ~v1_finset_1(X1)) )),
% 0.16/0.45    inference(cnf_transformation,[],[f9])).
% 0.16/0.45  fof(f9,plain,(
% 0.16/0.45    ! [X0,X1] : (v1_finset_1(k3_xboole_0(X0,X1)) | ~v1_finset_1(X1))),
% 0.16/0.45    inference(ennf_transformation,[],[f5])).
% 0.16/0.45  fof(f5,axiom,(
% 0.16/0.45    ! [X0,X1] : (v1_finset_1(X1) => v1_finset_1(k3_xboole_0(X0,X1)))),
% 0.16/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_finset_1)).
% 0.16/0.45  fof(f17,plain,(
% 0.16/0.45    v1_finset_1(sK0)),
% 0.16/0.45    inference(cnf_transformation,[],[f11])).
% 0.16/0.45  % SZS output end Proof for theBenchmark
% 0.16/0.45  % (31760)------------------------------
% 0.16/0.45  % (31760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.45  % (31760)Termination reason: Refutation
% 0.16/0.45  
% 0.16/0.45  % (31760)Memory used [KB]: 1918
% 0.16/0.45  % (31760)Time elapsed: 0.066 s
% 0.16/0.45  % (31760)------------------------------
% 0.16/0.45  % (31760)------------------------------
% 0.16/0.45  % (31746)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.16/0.45  % (31735)Success in time 0.138 s
%------------------------------------------------------------------------------

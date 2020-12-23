%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:52 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 141 expanded)
%              Number of leaves         :    7 (  44 expanded)
%              Depth                    :   20
%              Number of atoms          :  168 ( 715 expanded)
%              Number of equality atoms :   22 (  95 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(subsumption_resolution,[],[f42,f18])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ! [X1] :
        ( ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
          & r2_hidden(sK1(X1),k3_relat_1(sK0)) )
        | ~ r2_hidden(X1,k3_relat_1(sK0)) )
    & k1_xboole_0 != k3_relat_1(sK0)
    & v2_wellord1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
        & k3_relat_1(X0) != k1_xboole_0
        & v2_wellord1(X0)
        & v1_relat_1(X0) )
   => ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),sK0)
              & r2_hidden(X2,k3_relat_1(sK0)) )
          | ~ r2_hidden(X1,k3_relat_1(sK0)) )
      & k1_xboole_0 != k3_relat_1(sK0)
      & v2_wellord1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X1,X2),sK0)
          & r2_hidden(X2,k3_relat_1(sK0)) )
     => ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
        & r2_hidden(sK1(X1),k3_relat_1(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),X0)
              & r2_hidden(X2,k3_relat_1(X0)) )
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      & k3_relat_1(X0) != k1_xboole_0
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),X0)
              & r2_hidden(X2,k3_relat_1(X0)) )
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      & k3_relat_1(X0) != k1_xboole_0
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ~ ( ! [X1] :
                ~ ( ! [X2] :
                      ( r2_hidden(X2,k3_relat_1(X0))
                     => r2_hidden(k4_tarski(X1,X2),X0) )
                  & r2_hidden(X1,k3_relat_1(X0)) )
            & k3_relat_1(X0) != k1_xboole_0
            & v2_wellord1(X0) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ~ ( ! [X1] :
              ~ ( ! [X2] :
                    ( r2_hidden(X2,k3_relat_1(X0))
                   => r2_hidden(k4_tarski(X1,X2),X0) )
                & r2_hidden(X1,k3_relat_1(X0)) )
          & k3_relat_1(X0) != k1_xboole_0
          & v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord1)).

fof(f42,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f41,f19])).

fof(f19,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,
    ( ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f40,f28])).

fof(f28,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f26,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f39,f20])).

fof(f20,plain,(
    k1_xboole_0 != k3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,
    ( k1_xboole_0 = k3_relat_1(sK0)
    | ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f38,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X3] :
                ( r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(sK2(X0,X1),X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).

fof(f38,plain,(
    ~ r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    inference(resolution,[],[f37,f21])).

fof(f21,plain,(
    ! [X1] :
      ( r2_hidden(sK1(X1),k3_relat_1(sK0))
      | ~ r2_hidden(X1,k3_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    ~ r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f36,f18])).

fof(f36,plain,
    ( ~ r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f35,f19])).

fof(f35,plain,
    ( ~ r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f34,f20])).

fof(f34,plain,
    ( ~ r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0))
    | k1_xboole_0 = k3_relat_1(sK0)
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f33,f28])).

fof(f33,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | ~ r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0))
    | k1_xboole_0 = k3_relat_1(sK0)
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | ~ r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0))
    | k1_xboole_0 = k3_relat_1(sK0)
    | k1_xboole_0 = k3_relat_1(sK0)
    | ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f31,f23])).

fof(f31,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(sK0,X0),k3_relat_1(sK0))
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | ~ r2_hidden(sK1(sK2(sK0,X0)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f30,f22])).

fof(f22,plain,(
    ! [X1] :
      ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
      | ~ r2_hidden(X1,k3_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(sK0,X1),X0),sK0)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(sK0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f29,f18])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(sK0))
      | r2_hidden(k4_tarski(sK2(sK0,X1),X0),sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f24,f19])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_wellord1(X0)
      | ~ r2_hidden(X3,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:54:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (1241)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (1221)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (1221)Refutation not found, incomplete strategy% (1221)------------------------------
% 0.22/0.51  % (1221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1221)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (1221)Memory used [KB]: 10618
% 0.22/0.51  % (1221)Time elapsed: 0.085 s
% 0.22/0.51  % (1221)------------------------------
% 0.22/0.51  % (1221)------------------------------
% 0.22/0.51  % (1229)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (1222)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (1229)Refutation not found, incomplete strategy% (1229)------------------------------
% 0.22/0.51  % (1229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1229)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (1229)Memory used [KB]: 10618
% 0.22/0.51  % (1229)Time elapsed: 0.100 s
% 0.22/0.51  % (1229)------------------------------
% 0.22/0.51  % (1229)------------------------------
% 1.22/0.51  % (1223)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.22/0.52  % (1224)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.22/0.52  % (1224)Refutation found. Thanks to Tanya!
% 1.22/0.52  % SZS status Theorem for theBenchmark
% 1.22/0.52  % SZS output start Proof for theBenchmark
% 1.22/0.52  fof(f43,plain,(
% 1.22/0.52    $false),
% 1.22/0.52    inference(subsumption_resolution,[],[f42,f18])).
% 1.22/0.52  fof(f18,plain,(
% 1.22/0.52    v1_relat_1(sK0)),
% 1.22/0.52    inference(cnf_transformation,[],[f13])).
% 1.22/0.52  fof(f13,plain,(
% 1.22/0.52    ! [X1] : ((~r2_hidden(k4_tarski(X1,sK1(X1)),sK0) & r2_hidden(sK1(X1),k3_relat_1(sK0))) | ~r2_hidden(X1,k3_relat_1(sK0))) & k1_xboole_0 != k3_relat_1(sK0) & v2_wellord1(sK0) & v1_relat_1(sK0)),
% 1.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12,f11])).
% 1.22/0.52  fof(f11,plain,(
% 1.22/0.52    ? [X0] : (! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) | ~r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0) & v1_relat_1(X0)) => (! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),sK0) & r2_hidden(X2,k3_relat_1(sK0))) | ~r2_hidden(X1,k3_relat_1(sK0))) & k1_xboole_0 != k3_relat_1(sK0) & v2_wellord1(sK0) & v1_relat_1(sK0))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f12,plain,(
% 1.22/0.52    ! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),sK0) & r2_hidden(X2,k3_relat_1(sK0))) => (~r2_hidden(k4_tarski(X1,sK1(X1)),sK0) & r2_hidden(sK1(X1),k3_relat_1(sK0))))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f7,plain,(
% 1.22/0.52    ? [X0] : (! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) | ~r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0) & v1_relat_1(X0))),
% 1.22/0.52    inference(flattening,[],[f6])).
% 1.22/0.52  fof(f6,plain,(
% 1.22/0.52    ? [X0] : ((! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) | ~r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0)) & v1_relat_1(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f4])).
% 1.22/0.52  fof(f4,negated_conjecture,(
% 1.22/0.52    ~! [X0] : (v1_relat_1(X0) => ~(! [X1] : ~(! [X2] : (r2_hidden(X2,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X2),X0)) & r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0)))),
% 1.22/0.52    inference(negated_conjecture,[],[f3])).
% 1.22/0.52  fof(f3,conjecture,(
% 1.22/0.52    ! [X0] : (v1_relat_1(X0) => ~(! [X1] : ~(! [X2] : (r2_hidden(X2,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X2),X0)) & r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0)))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord1)).
% 1.22/0.52  fof(f42,plain,(
% 1.22/0.52    ~v1_relat_1(sK0)),
% 1.22/0.52    inference(subsumption_resolution,[],[f41,f19])).
% 1.22/0.52  fof(f19,plain,(
% 1.22/0.52    v2_wellord1(sK0)),
% 1.22/0.52    inference(cnf_transformation,[],[f13])).
% 1.22/0.52  fof(f41,plain,(
% 1.22/0.52    ~v2_wellord1(sK0) | ~v1_relat_1(sK0)),
% 1.22/0.52    inference(subsumption_resolution,[],[f40,f28])).
% 1.22/0.52  fof(f28,plain,(
% 1.22/0.52    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f27])).
% 1.22/0.52  fof(f27,plain,(
% 1.22/0.52    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.22/0.52    inference(resolution,[],[f26,f25])).
% 1.22/0.52  fof(f25,plain,(
% 1.22/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f17])).
% 1.22/0.52  fof(f17,plain,(
% 1.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f16])).
% 1.22/0.52  fof(f16,plain,(
% 1.22/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f10,plain,(
% 1.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.22/0.52    inference(ennf_transformation,[],[f5])).
% 1.22/0.52  fof(f5,plain,(
% 1.22/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.22/0.52    inference(unused_predicate_definition_removal,[],[f1])).
% 1.22/0.52  fof(f1,axiom,(
% 1.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.22/0.52  fof(f26,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f17])).
% 1.22/0.52  fof(f40,plain,(
% 1.22/0.52    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | ~v2_wellord1(sK0) | ~v1_relat_1(sK0)),
% 1.22/0.52    inference(subsumption_resolution,[],[f39,f20])).
% 1.22/0.52  fof(f20,plain,(
% 1.22/0.52    k1_xboole_0 != k3_relat_1(sK0)),
% 1.22/0.52    inference(cnf_transformation,[],[f13])).
% 1.22/0.52  fof(f39,plain,(
% 1.22/0.52    k1_xboole_0 = k3_relat_1(sK0) | ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | ~v2_wellord1(sK0) | ~v1_relat_1(sK0)),
% 1.22/0.52    inference(resolution,[],[f38,f23])).
% 1.22/0.52  fof(f23,plain,(
% 1.22/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f15])).
% 1.22/0.52  fof(f15,plain,(
% 1.22/0.52    ! [X0] : (! [X1] : ((! [X3] : (r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 1.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f14])).
% 1.22/0.52  fof(f14,plain,(
% 1.22/0.52    ! [X1,X0] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X1)))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f9,plain,(
% 1.22/0.52    ! [X0] : (! [X1] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 1.22/0.52    inference(flattening,[],[f8])).
% 1.22/0.52  fof(f8,plain,(
% 1.22/0.52    ! [X0] : ((! [X1] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f2])).
% 1.22/0.52  fof(f2,axiom,(
% 1.22/0.52    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(! [X2] : ~(! [X3] : (r2_hidden(X3,X1) => r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X2,X1)) & k1_xboole_0 != X1 & r1_tarski(X1,k3_relat_1(X0)))))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).
% 1.22/0.52  fof(f38,plain,(
% 1.22/0.52    ~r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))),
% 1.22/0.52    inference(resolution,[],[f37,f21])).
% 1.22/0.52  fof(f21,plain,(
% 1.22/0.52    ( ! [X1] : (r2_hidden(sK1(X1),k3_relat_1(sK0)) | ~r2_hidden(X1,k3_relat_1(sK0))) )),
% 1.22/0.52    inference(cnf_transformation,[],[f13])).
% 1.22/0.52  fof(f37,plain,(
% 1.22/0.52    ~r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0))),
% 1.22/0.52    inference(subsumption_resolution,[],[f36,f18])).
% 1.22/0.52  fof(f36,plain,(
% 1.22/0.52    ~r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 1.22/0.52    inference(subsumption_resolution,[],[f35,f19])).
% 1.22/0.52  fof(f35,plain,(
% 1.22/0.52    ~r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0)) | ~v2_wellord1(sK0) | ~v1_relat_1(sK0)),
% 1.22/0.52    inference(subsumption_resolution,[],[f34,f20])).
% 1.22/0.52  fof(f34,plain,(
% 1.22/0.52    ~r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0)) | k1_xboole_0 = k3_relat_1(sK0) | ~v2_wellord1(sK0) | ~v1_relat_1(sK0)),
% 1.22/0.52    inference(subsumption_resolution,[],[f33,f28])).
% 1.22/0.52  fof(f33,plain,(
% 1.22/0.52    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | ~r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0)) | k1_xboole_0 = k3_relat_1(sK0) | ~v2_wellord1(sK0) | ~v1_relat_1(sK0)),
% 1.22/0.52    inference(duplicate_literal_removal,[],[f32])).
% 1.22/0.52  fof(f32,plain,(
% 1.22/0.52    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | ~r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0)) | k1_xboole_0 = k3_relat_1(sK0) | k1_xboole_0 = k3_relat_1(sK0) | ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | ~v2_wellord1(sK0) | ~v1_relat_1(sK0)),
% 1.22/0.52    inference(resolution,[],[f31,f23])).
% 1.22/0.52  fof(f31,plain,(
% 1.22/0.52    ( ! [X0] : (~r2_hidden(sK2(sK0,X0),k3_relat_1(sK0)) | ~r1_tarski(X0,k3_relat_1(sK0)) | ~r2_hidden(sK1(sK2(sK0,X0)),X0) | k1_xboole_0 = X0) )),
% 1.22/0.52    inference(resolution,[],[f30,f22])).
% 1.22/0.52  fof(f22,plain,(
% 1.22/0.52    ( ! [X1] : (~r2_hidden(k4_tarski(X1,sK1(X1)),sK0) | ~r2_hidden(X1,k3_relat_1(sK0))) )),
% 1.22/0.52    inference(cnf_transformation,[],[f13])).
% 1.22/0.52  fof(f30,plain,(
% 1.22/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(sK0,X1),X0),sK0) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(sK0)) | ~r2_hidden(X0,X1)) )),
% 1.22/0.52    inference(subsumption_resolution,[],[f29,f18])).
% 1.22/0.52  fof(f29,plain,(
% 1.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK2(sK0,X1),X0),sK0) | ~v1_relat_1(sK0)) )),
% 1.22/0.52    inference(resolution,[],[f24,f19])).
% 1.22/0.52  fof(f24,plain,(
% 1.22/0.52    ( ! [X0,X3,X1] : (~v2_wellord1(X0) | ~r2_hidden(X3,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~v1_relat_1(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f15])).
% 1.22/0.52  % SZS output end Proof for theBenchmark
% 1.22/0.52  % (1224)------------------------------
% 1.22/0.52  % (1224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (1224)Termination reason: Refutation
% 1.22/0.52  
% 1.22/0.52  % (1224)Memory used [KB]: 6140
% 1.22/0.52  % (1224)Time elapsed: 0.100 s
% 1.22/0.52  % (1224)------------------------------
% 1.22/0.52  % (1224)------------------------------
% 1.22/0.52  % (1218)Success in time 0.153 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:52:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 272 expanded)
%              Number of leaves         :    7 (  66 expanded)
%              Depth                    :   17
%              Number of atoms          :  169 (1025 expanded)
%              Number of equality atoms :   31 ( 246 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(subsumption_resolution,[],[f195,f171])).

fof(f171,plain,(
    r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0) ),
    inference(subsumption_resolution,[],[f170,f45])).

fof(f45,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,X2))) ) ),
    inference(resolution,[],[f27,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(k1_relat_1(sK1),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(k1_relat_1(sK1),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_1)).

fof(f170,plain,
    ( r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0)
    | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_relat_1(k7_relat_1(sK1,sK0)) != X0
      | r2_hidden(sK2(sK0,k1_relat_1(sK1),X0),sK0)
      | r2_hidden(sK2(sK0,k1_relat_1(sK1),X0),X0) ) ),
    inference(superposition,[],[f48,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

% (30289)Refutation not found, incomplete strategy% (30289)------------------------------
% (30289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30289)Termination reason: Refutation not found, incomplete strategy

% (30289)Memory used [KB]: 10618
% (30289)Time elapsed: 0.116 s
% (30289)------------------------------
% (30289)------------------------------
% (30315)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (30303)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (30318)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (30304)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (30312)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (30320)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (30296)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (30312)Refutation not found, incomplete strategy% (30312)------------------------------
% (30312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30312)Termination reason: Refutation not found, incomplete strategy

% (30312)Memory used [KB]: 10746
% (30312)Time elapsed: 0.092 s
% (30312)------------------------------
% (30312)------------------------------
% (30313)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (30305)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (30316)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (30296)Refutation not found, incomplete strategy% (30296)------------------------------
% (30296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30307)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (30307)Refutation not found, incomplete strategy% (30307)------------------------------
% (30307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30307)Termination reason: Refutation not found, incomplete strategy

% (30307)Memory used [KB]: 10618
% (30307)Time elapsed: 0.147 s
% (30307)------------------------------
% (30307)------------------------------
% (30296)Termination reason: Refutation not found, incomplete strategy

% (30296)Memory used [KB]: 10618
% (30296)Time elapsed: 0.141 s
% (30296)------------------------------
% (30296)------------------------------
% (30315)Refutation not found, incomplete strategy% (30315)------------------------------
% (30315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30315)Termination reason: Refutation not found, incomplete strategy

% (30315)Memory used [KB]: 6268
% (30315)Time elapsed: 0.139 s
% (30315)------------------------------
% (30315)------------------------------
% (30295)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (30298)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f25,plain,(
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

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f48,plain,(
    k3_xboole_0(sK0,k1_relat_1(sK1)) != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(backward_demodulation,[],[f43,f44])).

fof(f44,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    inference(resolution,[],[f27,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f43,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f28,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f28,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f195,plain,(
    ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0) ),
    inference(subsumption_resolution,[],[f180,f194])).

fof(f194,plain,(
    r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f179,f48])).

fof(f179,plain,
    ( k3_xboole_0(sK0,k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,sK0))
    | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) ),
    inference(resolution,[],[f177,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f177,plain,(
    ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f176,f46])).

fof(f46,plain,(
    ! [X4,X3] :
      ( r2_hidden(X3,k1_relat_1(sK1))
      | ~ r2_hidden(X3,k1_relat_1(k7_relat_1(sK1,X4))) ) ),
    inference(resolution,[],[f27,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f176,plain,
    ( ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f172,f48])).

fof(f172,plain,
    ( k3_xboole_0(sK0,k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f171,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f180,plain,
    ( ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0) ),
    inference(resolution,[],[f177,f47])).

fof(f47,plain,(
    ! [X6,X5] :
      ( r2_hidden(X5,k1_relat_1(k7_relat_1(sK1,X6)))
      | ~ r2_hidden(X5,k1_relat_1(sK1))
      | ~ r2_hidden(X5,X6) ) ),
    inference(resolution,[],[f27,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:07:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (30310)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (30287)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (30301)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (30301)Refutation not found, incomplete strategy% (30301)------------------------------
% 0.20/0.51  % (30301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (30288)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (30309)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (30291)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (30300)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (30290)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (30300)Refutation not found, incomplete strategy% (30300)------------------------------
% 0.20/0.52  % (30300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (30300)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (30300)Memory used [KB]: 10618
% 0.20/0.52  % (30300)Time elapsed: 0.108 s
% 0.20/0.52  % (30300)------------------------------
% 0.20/0.52  % (30300)------------------------------
% 0.20/0.52  % (30301)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (30301)Memory used [KB]: 10618
% 0.20/0.52  % (30301)Time elapsed: 0.092 s
% 0.20/0.52  % (30301)------------------------------
% 0.20/0.52  % (30301)------------------------------
% 0.20/0.52  % (30306)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (30291)Refutation not found, incomplete strategy% (30291)------------------------------
% 0.20/0.53  % (30291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (30294)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (30291)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (30291)Memory used [KB]: 6140
% 0.20/0.53  % (30291)Time elapsed: 0.098 s
% 0.20/0.53  % (30291)------------------------------
% 0.20/0.53  % (30291)------------------------------
% 0.20/0.53  % (30311)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (30317)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (30302)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (30314)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (30308)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (30289)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (30292)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (30287)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f196,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f195,f171])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f170,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X2,X1] : (r2_hidden(X1,X2) | ~r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,X2)))) )),
% 0.20/0.53    inference(resolution,[],[f27,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    v1_relat_1(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(k1_relat_1(sK1),sK0) & v1_relat_1(sK1)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ? [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(k1_relat_1(sK1),sK0) & v1_relat_1(sK1))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0) & v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ~! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.53    inference(pure_predicate_removal,[],[f13])).
% 0.20/0.53  fof(f13,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.53    inference(negated_conjecture,[],[f12])).
% 0.20/0.53  fof(f12,conjecture,(
% 0.20/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_1)).
% 0.20/0.53  fof(f170,plain,(
% 0.20/0.53    r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.20/0.53    inference(equality_resolution,[],[f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,sK0)) != X0 | r2_hidden(sK2(sK0,k1_relat_1(sK1),X0),sK0) | r2_hidden(sK2(sK0,k1_relat_1(sK1),X0),X0)) )),
% 0.20/0.53    inference(superposition,[],[f48,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 0.20/0.54  % (30289)Refutation not found, incomplete strategy% (30289)------------------------------
% 0.20/0.54  % (30289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (30289)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (30289)Memory used [KB]: 10618
% 0.20/0.54  % (30289)Time elapsed: 0.116 s
% 0.20/0.54  % (30289)------------------------------
% 0.20/0.54  % (30289)------------------------------
% 0.20/0.54  % (30315)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (30303)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (30318)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (30304)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (30312)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (30320)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (30296)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (30312)Refutation not found, incomplete strategy% (30312)------------------------------
% 0.20/0.54  % (30312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (30312)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (30312)Memory used [KB]: 10746
% 0.20/0.54  % (30312)Time elapsed: 0.092 s
% 0.20/0.54  % (30312)------------------------------
% 0.20/0.54  % (30312)------------------------------
% 0.20/0.54  % (30313)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (30305)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (30316)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (30296)Refutation not found, incomplete strategy% (30296)------------------------------
% 0.20/0.55  % (30296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (30307)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (30307)Refutation not found, incomplete strategy% (30307)------------------------------
% 0.20/0.55  % (30307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (30307)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (30307)Memory used [KB]: 10618
% 0.20/0.55  % (30307)Time elapsed: 0.147 s
% 0.20/0.55  % (30307)------------------------------
% 0.20/0.55  % (30307)------------------------------
% 0.20/0.55  % (30296)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (30296)Memory used [KB]: 10618
% 0.20/0.55  % (30296)Time elapsed: 0.141 s
% 0.20/0.55  % (30296)------------------------------
% 0.20/0.55  % (30296)------------------------------
% 0.20/0.55  % (30315)Refutation not found, incomplete strategy% (30315)------------------------------
% 0.20/0.55  % (30315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (30315)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (30315)Memory used [KB]: 6268
% 0.20/0.55  % (30315)Time elapsed: 0.139 s
% 0.20/0.55  % (30315)------------------------------
% 0.20/0.55  % (30315)------------------------------
% 0.20/0.55  % (30295)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (30298)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.56  fof(f25,plain,(
% 1.50/0.56    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.50/0.56    introduced(choice_axiom,[])).
% 1.50/0.56  fof(f24,plain,(
% 1.50/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.50/0.56    inference(rectify,[],[f23])).
% 1.50/0.56  fof(f23,plain,(
% 1.50/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.50/0.56    inference(flattening,[],[f22])).
% 1.50/0.56  fof(f22,plain,(
% 1.50/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.50/0.56    inference(nnf_transformation,[],[f2])).
% 1.50/0.56  fof(f2,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.50/0.56  fof(f48,plain,(
% 1.50/0.56    k3_xboole_0(sK0,k1_relat_1(sK1)) != k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.50/0.56    inference(backward_demodulation,[],[f43,f44])).
% 1.50/0.56  fof(f44,plain,(
% 1.50/0.56    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) )),
% 1.50/0.56    inference(resolution,[],[f27,f33])).
% 1.50/0.56  fof(f33,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f17])).
% 1.50/0.56  fof(f17,plain,(
% 1.50/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.50/0.56    inference(ennf_transformation,[],[f11])).
% 1.50/0.56  fof(f11,axiom,(
% 1.50/0.56    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.50/0.56  fof(f43,plain,(
% 1.50/0.56    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(sK0,k1_relat_1(sK1))),
% 1.50/0.56    inference(forward_demodulation,[],[f28,f29])).
% 1.50/0.56  fof(f29,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f1])).
% 1.50/0.56  fof(f1,axiom,(
% 1.50/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.50/0.56  fof(f28,plain,(
% 1.50/0.56    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(k1_relat_1(sK1),sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f19])).
% 1.50/0.56  fof(f195,plain,(
% 1.50/0.56    ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0)),
% 1.50/0.56    inference(subsumption_resolution,[],[f180,f194])).
% 1.50/0.56  fof(f194,plain,(
% 1.50/0.56    r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))),
% 1.50/0.56    inference(subsumption_resolution,[],[f179,f48])).
% 1.50/0.56  fof(f179,plain,(
% 1.50/0.56    k3_xboole_0(sK0,k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,sK0)) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))),
% 1.50/0.56    inference(resolution,[],[f177,f38])).
% 1.50/0.56  fof(f38,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f177,plain,(
% 1.50/0.56    ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.50/0.56    inference(subsumption_resolution,[],[f176,f46])).
% 1.50/0.56  fof(f46,plain,(
% 1.50/0.56    ( ! [X4,X3] : (r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(X3,k1_relat_1(k7_relat_1(sK1,X4)))) )),
% 1.50/0.56    inference(resolution,[],[f27,f31])).
% 1.50/0.56  fof(f31,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f21])).
% 1.50/0.56  fof(f176,plain,(
% 1.50/0.56    ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.50/0.56    inference(subsumption_resolution,[],[f172,f48])).
% 1.50/0.56  fof(f172,plain,(
% 1.50/0.56    k3_xboole_0(sK0,k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,sK0)) | ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.50/0.56    inference(resolution,[],[f171,f39])).
% 1.50/0.56  fof(f39,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f180,plain,(
% 1.50/0.56    ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0)),
% 1.50/0.56    inference(resolution,[],[f177,f47])).
% 1.50/0.56  fof(f47,plain,(
% 1.50/0.56    ( ! [X6,X5] : (r2_hidden(X5,k1_relat_1(k7_relat_1(sK1,X6))) | ~r2_hidden(X5,k1_relat_1(sK1)) | ~r2_hidden(X5,X6)) )),
% 1.50/0.56    inference(resolution,[],[f27,f32])).
% 1.50/0.56  fof(f32,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f21])).
% 1.50/0.56  % SZS output end Proof for theBenchmark
% 1.50/0.56  % (30287)------------------------------
% 1.50/0.56  % (30287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (30287)Termination reason: Refutation
% 1.50/0.56  
% 1.50/0.56  % (30287)Memory used [KB]: 1918
% 1.50/0.56  % (30287)Time elapsed: 0.132 s
% 1.50/0.56  % (30287)------------------------------
% 1.50/0.56  % (30287)------------------------------
% 1.50/0.56  % (30280)Success in time 0.192 s
%------------------------------------------------------------------------------

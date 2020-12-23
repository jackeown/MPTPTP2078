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
% DateTime   : Thu Dec  3 12:52:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 254 expanded)
%              Number of leaves         :    6 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  166 (1007 expanded)
%              Number of equality atoms :   28 ( 228 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(subsumption_resolution,[],[f187,f163])).

fof(f163,plain,(
    r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0) ),
    inference(subsumption_resolution,[],[f162,f39])).

fof(f39,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,X2))) ) ),
    inference(resolution,[],[f23,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(k1_relat_1(sK1),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(k1_relat_1(sK1),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).

fof(f162,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0)
    | r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X1] :
      ( k1_relat_1(k7_relat_1(sK1,sK0)) != X1
      | r2_hidden(sK2(k1_relat_1(sK1),sK0,X1),sK0)
      | r2_hidden(sK2(k1_relat_1(sK1),sK0,X1),X1) ) ),
    inference(superposition,[],[f42,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
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

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f42,plain,(
    k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(backward_demodulation,[],[f24,f38])).

fof(f38,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    inference(resolution,[],[f23,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f24,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f187,plain,(
    ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0) ),
    inference(subsumption_resolution,[],[f172,f186])).

fof(f186,plain,(
    r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f170,f42])).

fof(f170,plain,
    ( k3_xboole_0(k1_relat_1(sK1),sK0) = k1_relat_1(k7_relat_1(sK1,sK0))
    | r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) ),
    inference(resolution,[],[f169,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f169,plain,(
    ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f168,f40])).

fof(f40,plain,(
    ! [X4,X3] :
      ( r2_hidden(X3,k1_relat_1(sK1))
      | ~ r2_hidden(X3,k1_relat_1(k7_relat_1(sK1,X4))) ) ),
    inference(resolution,[],[f23,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f168,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f164,f42])).

fof(f164,plain,
    ( k3_xboole_0(k1_relat_1(sK1),sK0) = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f163,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f172,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0) ),
    inference(resolution,[],[f169,f41])).

fof(f41,plain,(
    ! [X6,X5] :
      ( r2_hidden(X5,k1_relat_1(k7_relat_1(sK1,X6)))
      | ~ r2_hidden(X5,k1_relat_1(sK1))
      | ~ r2_hidden(X5,X6) ) ),
    inference(resolution,[],[f23,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:48:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (27518)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (27511)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (27508)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (27527)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (27529)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (27518)Refutation not found, incomplete strategy% (27518)------------------------------
% 0.22/0.54  % (27518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27518)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27518)Memory used [KB]: 10618
% 0.22/0.54  % (27518)Time elapsed: 0.089 s
% 0.22/0.54  % (27518)------------------------------
% 0.22/0.54  % (27518)------------------------------
% 0.22/0.54  % (27529)Refutation not found, incomplete strategy% (27529)------------------------------
% 0.22/0.54  % (27529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27529)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27529)Memory used [KB]: 10746
% 0.22/0.54  % (27529)Time elapsed: 0.129 s
% 0.22/0.54  % (27529)------------------------------
% 0.22/0.54  % (27529)------------------------------
% 0.22/0.54  % (27523)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (27528)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (27519)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (27519)Refutation not found, incomplete strategy% (27519)------------------------------
% 0.22/0.55  % (27519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27519)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (27519)Memory used [KB]: 10618
% 0.22/0.55  % (27519)Time elapsed: 0.094 s
% 0.22/0.55  % (27519)------------------------------
% 0.22/0.55  % (27519)------------------------------
% 0.22/0.55  % (27508)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f188,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f187,f163])).
% 0.22/0.55  fof(f163,plain,(
% 0.22/0.55    r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f162,f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ( ! [X2,X1] : (r2_hidden(X1,X2) | ~r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,X2)))) )),
% 0.22/0.55    inference(resolution,[],[f23,f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(flattening,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(nnf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    v1_relat_1(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(k1_relat_1(sK1),sK0) & v1_relat_1(sK1)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ? [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(k1_relat_1(sK1),sK0) & v1_relat_1(sK1))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ? [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0) & v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ~! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.55    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.55  fof(f9,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.55    inference(negated_conjecture,[],[f8])).
% 0.22/0.55  fof(f8,conjecture,(
% 0.22/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).
% 0.22/0.55  fof(f162,plain,(
% 0.22/0.55    r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0) | r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.22/0.55    inference(equality_resolution,[],[f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,sK0)) != X1 | r2_hidden(sK2(k1_relat_1(sK1),sK0,X1),sK0) | r2_hidden(sK2(k1_relat_1(sK1),sK0,X1),X1)) )),
% 0.22/0.55    inference(superposition,[],[f42,f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.55    inference(rectify,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.55    inference(flattening,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.55    inference(nnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.55    inference(backward_demodulation,[],[f24,f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) )),
% 0.22/0.55    inference(resolution,[],[f23,f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f187,plain,(
% 0.22/0.55    ~r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f172,f186])).
% 0.22/0.55  fof(f186,plain,(
% 0.22/0.55    r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f170,f42])).
% 0.22/0.55  fof(f170,plain,(
% 0.22/0.55    k3_xboole_0(k1_relat_1(sK1),sK0) = k1_relat_1(k7_relat_1(sK1,sK0)) | r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))),
% 0.22/0.55    inference(resolution,[],[f169,f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f169,plain,(
% 0.22/0.55    ~r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f168,f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ( ! [X4,X3] : (r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(X3,k1_relat_1(k7_relat_1(sK1,X4)))) )),
% 0.22/0.55    inference(resolution,[],[f23,f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f168,plain,(
% 0.22/0.55    ~r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | ~r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f164,f42])).
% 0.22/0.55  fof(f164,plain,(
% 0.22/0.55    k3_xboole_0(k1_relat_1(sK1),sK0) = k1_relat_1(k7_relat_1(sK1,sK0)) | ~r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | ~r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.22/0.55    inference(resolution,[],[f163,f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f172,plain,(
% 0.22/0.55    ~r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | ~r2_hidden(sK2(k1_relat_1(sK1),sK0,k1_relat_1(k7_relat_1(sK1,sK0))),sK0)),
% 0.22/0.55    inference(resolution,[],[f169,f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ( ! [X6,X5] : (r2_hidden(X5,k1_relat_1(k7_relat_1(sK1,X6))) | ~r2_hidden(X5,k1_relat_1(sK1)) | ~r2_hidden(X5,X6)) )),
% 0.22/0.55    inference(resolution,[],[f23,f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (27508)------------------------------
% 0.22/0.55  % (27508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27508)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (27508)Memory used [KB]: 1918
% 0.22/0.55  % (27508)Time elapsed: 0.145 s
% 0.22/0.55  % (27508)------------------------------
% 0.22/0.55  % (27508)------------------------------
% 0.22/0.55  % (27503)Success in time 0.187 s
%------------------------------------------------------------------------------

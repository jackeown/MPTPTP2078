%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 139 expanded)
%              Number of leaves         :    5 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 ( 667 expanded)
%              Number of equality atoms :   23 ( 123 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f744,plain,(
    $false ),
    inference(subsumption_resolution,[],[f660,f681])).

fof(f681,plain,(
    r2_hidden(sK2(k2_relat_1(sK1),sK0,k2_relat_1(k8_relat_1(sK0,sK1))),k2_relat_1(k8_relat_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f16,f76,f658,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(X0,k2_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(X0,k2_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_relat_1)).

fof(f658,plain,(
    r2_hidden(sK2(k2_relat_1(sK1),sK0,k2_relat_1(k8_relat_1(sK0,sK1))),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f17,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k2_relat_1(sK1),X0,k2_relat_1(k8_relat_1(X1,sK1))),k2_relat_1(sK1))
      | k2_relat_1(k8_relat_1(X1,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0) ) ),
    inference(factoring,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,k2_relat_1(k8_relat_1(X2,sK1))),k2_relat_1(sK1))
      | r2_hidden(sK2(X0,X1,k2_relat_1(k8_relat_1(X2,sK1))),X0)
      | k3_xboole_0(X0,X1) = k2_relat_1(k8_relat_1(X2,sK1)) ) ),
    inference(resolution,[],[f31,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f14])).

fof(f14,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f12])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f31,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k2_relat_1(k8_relat_1(X3,sK1)))
      | r2_hidden(X2,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f16,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      | r2_hidden(X0,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,plain,(
    k2_relat_1(k8_relat_1(sK0,sK1)) != k3_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( k2_relat_1(k8_relat_1(sK0,sK1)) != k3_xboole_0(k2_relat_1(sK1),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(k8_relat_1(X0,X1)) != k3_xboole_0(k2_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( k2_relat_1(k8_relat_1(sK0,sK1)) != k3_xboole_0(k2_relat_1(sK1),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != k3_xboole_0(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f76,plain,(
    r2_hidden(sK2(k2_relat_1(sK1),sK0,k2_relat_1(k8_relat_1(sK0,sK1))),sK0) ),
    inference(unit_resulting_resolution,[],[f17,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,k2_relat_1(k8_relat_1(X1,sK1))),X1)
      | k3_xboole_0(X0,X1) = k2_relat_1(k8_relat_1(X1,sK1)) ) ),
    inference(factoring,[],[f34])).

fof(f34,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK2(X3,X4,k2_relat_1(k8_relat_1(X5,sK1))),X5)
      | r2_hidden(sK2(X3,X4,k2_relat_1(k8_relat_1(X5,sK1))),X4)
      | k2_relat_1(k8_relat_1(X5,sK1)) = k3_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f30,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,sK1)))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f16,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f660,plain,(
    ~ r2_hidden(sK2(k2_relat_1(sK1),sK0,k2_relat_1(k8_relat_1(sK0,sK1))),k2_relat_1(k8_relat_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f17,f76,f658,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (26724)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (26722)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (26716)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (26715)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (26714)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (26723)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (26722)Refutation not found, incomplete strategy% (26722)------------------------------
% 0.21/0.50  % (26722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26722)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26722)Memory used [KB]: 10618
% 0.21/0.50  % (26722)Time elapsed: 0.073 s
% 0.21/0.50  % (26722)------------------------------
% 0.21/0.50  % (26722)------------------------------
% 0.21/0.50  % (26721)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.53  % (26720)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (26713)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (26719)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (26723)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (26719)Refutation not found, incomplete strategy% (26719)------------------------------
% 0.21/0.53  % (26719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26719)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26719)Memory used [KB]: 10490
% 0.21/0.53  % (26719)Time elapsed: 0.113 s
% 0.21/0.53  % (26719)------------------------------
% 0.21/0.53  % (26719)------------------------------
% 1.47/0.54  % (26727)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.47/0.54  % (26712)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.47/0.54  % (26710)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.47/0.54  % (26728)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.47/0.54  % (26728)Refutation not found, incomplete strategy% (26728)------------------------------
% 1.47/0.54  % (26728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.54  % (26728)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.54  
% 1.47/0.54  % (26728)Memory used [KB]: 10490
% 1.47/0.54  % (26728)Time elapsed: 0.120 s
% 1.47/0.54  % (26728)------------------------------
% 1.47/0.54  % (26728)------------------------------
% 1.47/0.54  % SZS output start Proof for theBenchmark
% 1.47/0.54  fof(f744,plain,(
% 1.47/0.54    $false),
% 1.47/0.54    inference(subsumption_resolution,[],[f660,f681])).
% 1.47/0.54  fof(f681,plain,(
% 1.47/0.54    r2_hidden(sK2(k2_relat_1(sK1),sK0,k2_relat_1(k8_relat_1(sK0,sK1))),k2_relat_1(k8_relat_1(sK0,sK1)))),
% 1.47/0.54    inference(unit_resulting_resolution,[],[f16,f76,f658,f20])).
% 1.47/0.54  fof(f20,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k2_relat_1(X2)) | ~r2_hidden(X0,X1) | r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))) )),
% 1.47/0.54    inference(cnf_transformation,[],[f10])).
% 1.47/0.54  fof(f10,plain,(
% 1.47/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | ~r2_hidden(X0,k2_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))))) | ~v1_relat_1(X2))),
% 1.47/0.54    inference(flattening,[],[f9])).
% 1.47/0.54  fof(f9,plain,(
% 1.47/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | (~r2_hidden(X0,k2_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))))) | ~v1_relat_1(X2))),
% 1.47/0.54    inference(nnf_transformation,[],[f6])).
% 1.47/0.54  fof(f6,plain,(
% 1.47/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 1.47/0.54    inference(ennf_transformation,[],[f2])).
% 1.47/0.54  fof(f2,axiom,(
% 1.47/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1))))),
% 1.47/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_relat_1)).
% 1.47/0.54  fof(f658,plain,(
% 1.47/0.54    r2_hidden(sK2(k2_relat_1(sK1),sK0,k2_relat_1(k8_relat_1(sK0,sK1))),k2_relat_1(sK1))),
% 1.47/0.54    inference(unit_resulting_resolution,[],[f17,f163])).
% 1.47/0.54  fof(f163,plain,(
% 1.47/0.54    ( ! [X0,X1] : (r2_hidden(sK2(k2_relat_1(sK1),X0,k2_relat_1(k8_relat_1(X1,sK1))),k2_relat_1(sK1)) | k2_relat_1(k8_relat_1(X1,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0)) )),
% 1.47/0.54    inference(factoring,[],[f37])).
% 1.47/0.54  fof(f37,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,k2_relat_1(k8_relat_1(X2,sK1))),k2_relat_1(sK1)) | r2_hidden(sK2(X0,X1,k2_relat_1(k8_relat_1(X2,sK1))),X0) | k3_xboole_0(X0,X1) = k2_relat_1(k8_relat_1(X2,sK1))) )),
% 1.47/0.54    inference(resolution,[],[f31,f24])).
% 1.47/0.54  fof(f24,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 1.47/0.54    inference(cnf_transformation,[],[f15])).
% 1.47/0.54  fof(f15,plain,(
% 1.47/0.54    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.47/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f14])).
% 1.47/0.54  fof(f14,plain,(
% 1.47/0.54    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.47/0.54    introduced(choice_axiom,[])).
% 1.47/0.54  fof(f13,plain,(
% 1.47/0.54    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.47/0.54    inference(rectify,[],[f12])).
% 1.47/0.54  fof(f12,plain,(
% 1.47/0.54    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.47/0.54    inference(flattening,[],[f11])).
% 1.47/0.54  fof(f11,plain,(
% 1.47/0.54    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.47/0.54    inference(nnf_transformation,[],[f1])).
% 1.47/0.54  fof(f1,axiom,(
% 1.47/0.54    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.47/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.47/0.54  fof(f31,plain,(
% 1.47/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k2_relat_1(k8_relat_1(X3,sK1))) | r2_hidden(X2,k2_relat_1(sK1))) )),
% 1.47/0.54    inference(resolution,[],[f16,f19])).
% 1.47/0.54  fof(f19,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | r2_hidden(X0,k2_relat_1(X2))) )),
% 1.47/0.54    inference(cnf_transformation,[],[f10])).
% 1.47/0.54  fof(f17,plain,(
% 1.47/0.54    k2_relat_1(k8_relat_1(sK0,sK1)) != k3_xboole_0(k2_relat_1(sK1),sK0)),
% 1.47/0.54    inference(cnf_transformation,[],[f8])).
% 1.47/0.54  fof(f8,plain,(
% 1.47/0.54    k2_relat_1(k8_relat_1(sK0,sK1)) != k3_xboole_0(k2_relat_1(sK1),sK0) & v1_relat_1(sK1)),
% 1.47/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f7])).
% 1.47/0.54  fof(f7,plain,(
% 1.47/0.54    ? [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) != k3_xboole_0(k2_relat_1(X1),X0) & v1_relat_1(X1)) => (k2_relat_1(k8_relat_1(sK0,sK1)) != k3_xboole_0(k2_relat_1(sK1),sK0) & v1_relat_1(sK1))),
% 1.47/0.54    introduced(choice_axiom,[])).
% 1.47/0.54  fof(f5,plain,(
% 1.47/0.54    ? [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) != k3_xboole_0(k2_relat_1(X1),X0) & v1_relat_1(X1))),
% 1.47/0.54    inference(ennf_transformation,[],[f4])).
% 1.47/0.54  fof(f4,negated_conjecture,(
% 1.47/0.54    ~! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 1.47/0.54    inference(negated_conjecture,[],[f3])).
% 1.47/0.54  fof(f3,conjecture,(
% 1.47/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 1.47/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 1.47/0.54  fof(f76,plain,(
% 1.47/0.54    r2_hidden(sK2(k2_relat_1(sK1),sK0,k2_relat_1(k8_relat_1(sK0,sK1))),sK0)),
% 1.47/0.54    inference(unit_resulting_resolution,[],[f17,f74])).
% 1.47/0.54  fof(f74,plain,(
% 1.47/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,k2_relat_1(k8_relat_1(X1,sK1))),X1) | k3_xboole_0(X0,X1) = k2_relat_1(k8_relat_1(X1,sK1))) )),
% 1.47/0.54    inference(factoring,[],[f34])).
% 1.47/0.54  fof(f34,plain,(
% 1.47/0.54    ( ! [X4,X5,X3] : (r2_hidden(sK2(X3,X4,k2_relat_1(k8_relat_1(X5,sK1))),X5) | r2_hidden(sK2(X3,X4,k2_relat_1(k8_relat_1(X5,sK1))),X4) | k2_relat_1(k8_relat_1(X5,sK1)) = k3_xboole_0(X3,X4)) )),
% 1.47/0.54    inference(resolution,[],[f30,f25])).
% 1.47/0.54  fof(f25,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | k3_xboole_0(X0,X1) = X2) )),
% 1.47/0.54    inference(cnf_transformation,[],[f15])).
% 1.47/0.54  fof(f30,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,sK1))) | r2_hidden(X0,X1)) )),
% 1.47/0.54    inference(resolution,[],[f16,f18])).
% 1.47/0.54  fof(f18,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | r2_hidden(X0,X1)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f10])).
% 1.47/0.54  fof(f16,plain,(
% 1.47/0.54    v1_relat_1(sK1)),
% 1.47/0.54    inference(cnf_transformation,[],[f8])).
% 1.47/0.54  fof(f660,plain,(
% 1.47/0.54    ~r2_hidden(sK2(k2_relat_1(sK1),sK0,k2_relat_1(k8_relat_1(sK0,sK1))),k2_relat_1(k8_relat_1(sK0,sK1)))),
% 1.47/0.54    inference(unit_resulting_resolution,[],[f17,f76,f658,f26])).
% 1.47/0.54  fof(f26,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 1.47/0.54    inference(cnf_transformation,[],[f15])).
% 1.47/0.54  % SZS output end Proof for theBenchmark
% 1.47/0.54  % (26723)------------------------------
% 1.47/0.54  % (26723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.54  % (26723)Termination reason: Refutation
% 1.47/0.54  
% 1.47/0.54  % (26723)Memory used [KB]: 7036
% 1.47/0.54  % (26723)Time elapsed: 0.096 s
% 1.47/0.54  % (26723)------------------------------
% 1.47/0.54  % (26723)------------------------------
% 1.47/0.54  % (26709)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.47/0.55  % (26707)Success in time 0.189 s
%------------------------------------------------------------------------------

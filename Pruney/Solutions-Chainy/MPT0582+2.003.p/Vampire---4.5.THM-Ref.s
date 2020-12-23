%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 113 expanded)
%              Number of leaves         :    5 (  21 expanded)
%              Depth                    :   14
%              Number of atoms          :  130 ( 420 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f267,plain,(
    $false ),
    inference(subsumption_resolution,[],[f262,f23])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & r1_tarski(k1_relat_1(X2),X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & r1_tarski(k1_relat_1(X2),X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( ( r1_tarski(X2,X1)
                & r1_tarski(k1_relat_1(X2),X0) )
             => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k1_relat_1(X2),X0) )
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_relat_1)).

fof(f262,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f261,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f261,plain,(
    ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f260,f198])).

fof(f198,plain,(
    r2_hidden(k4_tarski(sK3(sK2,k7_relat_1(sK1,sK0)),sK4(sK2,k7_relat_1(sK1,sK0))),sK1) ),
    inference(resolution,[],[f85,f74])).

fof(f74,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK2)
      | r2_hidden(k4_tarski(X1,X2),sK1) ) ),
    inference(subsumption_resolution,[],[f73,f19])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(k4_tarski(X1,X2),sK2)
      | r2_hidden(k4_tarski(X1,X2),sK1) ) ),
    inference(resolution,[],[f21,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f21,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f85,plain,(
    r2_hidden(k4_tarski(sK3(sK2,k7_relat_1(sK1,sK0)),sK4(sK2,k7_relat_1(sK1,sK0))),sK2) ),
    inference(subsumption_resolution,[],[f79,f19])).

fof(f79,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK3(sK2,k7_relat_1(sK1,sK0)),sK4(sK2,k7_relat_1(sK1,sK0))),sK2) ),
    inference(resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f22,plain,(
    ~ r1_tarski(sK2,k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f260,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ r2_hidden(k4_tarski(sK3(sK2,k7_relat_1(sK1,sK0)),sK4(sK2,k7_relat_1(sK1,sK0))),sK1) ),
    inference(subsumption_resolution,[],[f259,f197])).

fof(f197,plain,(
    r2_hidden(sK3(sK2,k7_relat_1(sK1,sK0)),sK0) ),
    inference(resolution,[],[f85,f107])).

fof(f107,plain,(
    ! [X14,X13] :
      ( ~ r2_hidden(k4_tarski(X13,X14),sK2)
      | r2_hidden(X13,sK0) ) ),
    inference(subsumption_resolution,[],[f102,f19])).

fof(f102,plain,(
    ! [X14,X13] :
      ( ~ r2_hidden(k4_tarski(X13,X14),sK2)
      | ~ v1_relat_1(sK2)
      | r2_hidden(X13,sK0) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X14,X13] :
      ( ~ r2_hidden(k4_tarski(X13,X14),sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK2)
      | r2_hidden(X13,sK0) ) ),
    inference(superposition,[],[f39,f78])).

fof(f78,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f75,f19])).

fof(f75,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k7_relat_1(sK2,sK0) ),
    inference(resolution,[],[f20,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f20,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f259,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ r2_hidden(sK3(sK2,k7_relat_1(sK1,sK0)),sK0)
    | ~ r2_hidden(k4_tarski(sK3(sK2,k7_relat_1(sK1,sK0)),sK4(sK2,k7_relat_1(sK1,sK0))),sK1) ),
    inference(subsumption_resolution,[],[f251,f23])).

fof(f251,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ r2_hidden(sK3(sK2,k7_relat_1(sK1,sK0)),sK0)
    | ~ r2_hidden(k4_tarski(sK3(sK2,k7_relat_1(sK1,sK0)),sK4(sK2,k7_relat_1(sK1,sK0))),sK1) ),
    inference(resolution,[],[f86,f37])).

fof(f37,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f86,plain,(
    ~ r2_hidden(k4_tarski(sK3(sK2,k7_relat_1(sK1,sK0)),sK4(sK2,k7_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f80,f19])).

fof(f80,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r2_hidden(k4_tarski(sK3(sK2,k7_relat_1(sK1,sK0)),sK4(sK2,k7_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f22,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (8556)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (8550)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (8548)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (8555)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (8551)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (8554)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (8566)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (8549)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (8560)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (8547)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (8557)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (8558)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (8547)Refutation not found, incomplete strategy% (8547)------------------------------
% 0.21/0.51  % (8547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8565)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (8564)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (8547)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8547)Memory used [KB]: 10490
% 0.21/0.51  % (8547)Time elapsed: 0.087 s
% 0.21/0.51  % (8547)------------------------------
% 0.21/0.51  % (8547)------------------------------
% 0.21/0.51  % (8566)Refutation not found, incomplete strategy% (8566)------------------------------
% 0.21/0.51  % (8566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8566)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8566)Memory used [KB]: 10490
% 0.21/0.51  % (8566)Time elapsed: 0.102 s
% 0.21/0.51  % (8566)------------------------------
% 0.21/0.51  % (8566)------------------------------
% 0.21/0.51  % (8553)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (8562)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (8552)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (8546)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (8559)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.53  % (8559)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f267,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f262,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    v1_relat_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k7_relat_1(X1,X0)) & (r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0)) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f7])).
% 0.21/0.53  fof(f7,conjecture,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0)) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_relat_1)).
% 0.21/0.53  fof(f262,plain,(
% 0.21/0.53    ~v1_relat_1(sK1)),
% 0.21/0.53    inference(resolution,[],[f261,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.53  fof(f261,plain,(
% 0.21/0.53    ~v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f260,f198])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK3(sK2,k7_relat_1(sK1,sK0)),sK4(sK2,k7_relat_1(sK1,sK0))),sK1)),
% 0.21/0.53    inference(resolution,[],[f85,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X1,X2),sK2) | r2_hidden(k4_tarski(X1,X2),sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f73,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    v1_relat_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~v1_relat_1(sK2) | ~r2_hidden(k4_tarski(X1,X2),sK2) | r2_hidden(k4_tarski(X1,X2),sK1)) )),
% 0.21/0.53    inference(resolution,[],[f21,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    r1_tarski(sK2,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK3(sK2,k7_relat_1(sK1,sK0)),sK4(sK2,k7_relat_1(sK1,sK0))),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f79,f19])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK3(sK2,k7_relat_1(sK1,sK0)),sK4(sK2,k7_relat_1(sK1,sK0))),sK2)),
% 0.21/0.53    inference(resolution,[],[f22,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ~r1_tarski(sK2,k7_relat_1(sK1,sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f260,plain,(
% 0.21/0.53    ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~r2_hidden(k4_tarski(sK3(sK2,k7_relat_1(sK1,sK0)),sK4(sK2,k7_relat_1(sK1,sK0))),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f259,f197])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    r2_hidden(sK3(sK2,k7_relat_1(sK1,sK0)),sK0)),
% 0.21/0.53    inference(resolution,[],[f85,f107])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ( ! [X14,X13] : (~r2_hidden(k4_tarski(X13,X14),sK2) | r2_hidden(X13,sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f102,f19])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ( ! [X14,X13] : (~r2_hidden(k4_tarski(X13,X14),sK2) | ~v1_relat_1(sK2) | r2_hidden(X13,sK0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f101])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ( ! [X14,X13] : (~r2_hidden(k4_tarski(X13,X14),sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(X13,sK0)) )),
% 0.21/0.53    inference(superposition,[],[f39,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    sK2 = k7_relat_1(sK2,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f75,f19])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ~v1_relat_1(sK2) | sK2 = k7_relat_1(sK2,sK0)),
% 0.21/0.53    inference(resolution,[],[f20,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2) | k7_relat_1(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~r2_hidden(sK3(sK2,k7_relat_1(sK1,sK0)),sK0) | ~r2_hidden(k4_tarski(sK3(sK2,k7_relat_1(sK1,sK0)),sK4(sK2,k7_relat_1(sK1,sK0))),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f251,f23])).
% 0.21/0.53  fof(f251,plain,(
% 0.21/0.53    ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~r2_hidden(sK3(sK2,k7_relat_1(sK1,sK0)),sK0) | ~r2_hidden(k4_tarski(sK3(sK2,k7_relat_1(sK1,sK0)),sK4(sK2,k7_relat_1(sK1,sK0))),sK1)),
% 0.21/0.53    inference(resolution,[],[f86,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X0) | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X0) | r2_hidden(k4_tarski(X3,X4),X2) | k7_relat_1(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ~r2_hidden(k4_tarski(sK3(sK2,k7_relat_1(sK1,sK0)),sK4(sK2,k7_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f80,f19])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ~v1_relat_1(sK2) | ~r2_hidden(k4_tarski(sK3(sK2,k7_relat_1(sK1,sK0)),sK4(sK2,k7_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0))),
% 0.21/0.53    inference(resolution,[],[f22,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (8559)------------------------------
% 0.21/0.53  % (8559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8559)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (8559)Memory used [KB]: 1663
% 0.21/0.53  % (8559)Time elapsed: 0.114 s
% 0.21/0.53  % (8559)------------------------------
% 0.21/0.53  % (8559)------------------------------
% 0.21/0.53  % (8537)Success in time 0.171 s
%------------------------------------------------------------------------------

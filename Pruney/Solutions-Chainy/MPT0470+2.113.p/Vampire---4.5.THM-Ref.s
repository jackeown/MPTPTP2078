%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  75 expanded)
%              Number of leaves         :    5 (  21 expanded)
%              Depth                    :   15
%              Number of atoms          :  122 ( 213 expanded)
%              Number of equality atoms :   35 (  55 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f892,plain,(
    $false ),
    inference(subsumption_resolution,[],[f889,f494])).

fof(f494,plain,(
    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f481])).

fof(f481,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f10,f478])).

fof(f478,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(resolution,[],[f477,f12])).

fof(f12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f477,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | k5_relat_1(k1_xboole_0,sK0) = X9 ) ),
    inference(subsumption_resolution,[],[f475,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f475,plain,(
    ! [X9] :
      ( r2_hidden(sK6(X9),X9)
      | k5_relat_1(k1_xboole_0,sK0) = X9
      | ~ v1_xboole_0(X9) ) ),
    inference(resolution,[],[f464,f20])).

fof(f464,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,X0),sK2(k1_xboole_0,sK0,X0)),X0)
      | r2_hidden(sK6(X0),X0)
      | k5_relat_1(k1_xboole_0,sK0) = X0 ) ),
    inference(resolution,[],[f462,f12])).

fof(f462,plain,(
    ! [X15,X16] :
      ( ~ v1_xboole_0(X15)
      | k5_relat_1(X15,sK0) = X16
      | r2_hidden(sK6(X16),X16)
      | r2_hidden(k4_tarski(sK1(X15,sK0,X16),sK2(X15,sK0,X16)),X16) ) ),
    inference(subsumption_resolution,[],[f448,f20])).

fof(f448,plain,(
    ! [X15,X16] :
      ( r2_hidden(k4_tarski(sK1(X15,sK0,X16),sK2(X15,sK0,X16)),X16)
      | k5_relat_1(X15,sK0) = X16
      | r2_hidden(sK6(X15),X15)
      | r2_hidden(sK6(X16),X16)
      | ~ v1_xboole_0(X15) ) ),
    inference(resolution,[],[f238,f20])).

fof(f238,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,sK0,X1),sK4(X0,sK0,X1)),X0)
      | r2_hidden(k4_tarski(sK1(X0,sK0,X1),sK2(X0,sK0,X1)),X1)
      | k5_relat_1(X0,sK0) = X1
      | r2_hidden(sK6(X0),X0)
      | r2_hidden(sK6(X1),X1) ) ),
    inference(resolution,[],[f76,f22])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK1(X1,sK0,X0),sK4(X1,sK0,X0)),X1)
      | r2_hidden(k4_tarski(sK1(X1,sK0,X0),sK2(X1,sK0,X0)),X0)
      | k5_relat_1(X1,sK0) = X0
      | r2_hidden(sK6(X1),X1) ) ),
    inference(resolution,[],[f31,f22])).

fof(f31,plain,(
    ! [X12,X11] :
      ( ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | r2_hidden(k4_tarski(sK1(X11,sK0,X12),sK4(X11,sK0,X12)),X11)
      | r2_hidden(k4_tarski(sK1(X11,sK0,X12),sK2(X11,sK0,X12)),X12)
      | k5_relat_1(X11,sK0) = X12 ) ),
    inference(resolution,[],[f11,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f11,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f10,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f889,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f888,f12])).

fof(f888,plain,(
    ! [X17] :
      ( ~ v1_xboole_0(X17)
      | k5_relat_1(sK0,k1_xboole_0) = X17 ) ),
    inference(subsumption_resolution,[],[f877,f20])).

fof(f877,plain,(
    ! [X17] :
      ( r2_hidden(sK6(X17),X17)
      | k5_relat_1(sK0,k1_xboole_0) = X17
      | ~ v1_xboole_0(X17) ) ),
    inference(resolution,[],[f860,f20])).

fof(f860,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(sK0,k1_xboole_0,X0),sK2(sK0,k1_xboole_0,X0)),X0)
      | r2_hidden(sK6(X0),X0)
      | k5_relat_1(sK0,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f858,f12])).

fof(f858,plain,(
    ! [X30,X29] :
      ( ~ v1_xboole_0(X29)
      | k5_relat_1(sK0,X29) = X30
      | r2_hidden(sK6(X30),X30)
      | r2_hidden(k4_tarski(sK1(sK0,X29,X30),sK2(sK0,X29,X30)),X30) ) ),
    inference(subsumption_resolution,[],[f836,f20])).

fof(f836,plain,(
    ! [X30,X29] :
      ( r2_hidden(k4_tarski(sK1(sK0,X29,X30),sK2(sK0,X29,X30)),X30)
      | k5_relat_1(sK0,X29) = X30
      | r2_hidden(sK6(X29),X29)
      | r2_hidden(sK6(X30),X30)
      | ~ v1_xboole_0(X29) ) ),
    inference(resolution,[],[f271,f20])).

fof(f271,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(sK0,X0,X1),sK2(sK0,X0,X1)),X0)
      | r2_hidden(k4_tarski(sK1(sK0,X0,X1),sK2(sK0,X0,X1)),X1)
      | k5_relat_1(sK0,X0) = X1
      | r2_hidden(sK6(X0),X0)
      | r2_hidden(sK6(X1),X1) ) ),
    inference(resolution,[],[f85,f22])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(sK0,X1,X0),sK2(sK0,X1,X0)),X1)
      | r2_hidden(k4_tarski(sK1(sK0,X1,X0),sK2(sK0,X1,X0)),X0)
      | k5_relat_1(sK0,X1) = X0
      | r2_hidden(sK6(X1),X1) ) ),
    inference(resolution,[],[f33,f22])).

fof(f33,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | r2_hidden(k4_tarski(sK4(sK0,X15,X16),sK2(sK0,X15,X16)),X15)
      | r2_hidden(k4_tarski(sK1(sK0,X15,X16),sK2(sK0,X15,X16)),X16)
      | k5_relat_1(sK0,X15) = X16 ) ),
    inference(resolution,[],[f11,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK2(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (27908)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (27907)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (27916)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (27915)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (27911)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (27905)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (27918)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (27920)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (27919)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (27913)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (27909)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (27918)Refutation not found, incomplete strategy% (27918)------------------------------
% 0.21/0.50  % (27918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27918)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (27918)Memory used [KB]: 6268
% 0.21/0.50  % (27918)Time elapsed: 0.043 s
% 0.21/0.50  % (27918)------------------------------
% 0.21/0.50  % (27918)------------------------------
% 0.21/0.50  % (27912)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (27904)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (27906)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (27921)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (27906)Refutation not found, incomplete strategy% (27906)------------------------------
% 0.21/0.50  % (27906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27906)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (27906)Memory used [KB]: 10618
% 0.21/0.50  % (27906)Time elapsed: 0.092 s
% 0.21/0.50  % (27906)------------------------------
% 0.21/0.50  % (27906)------------------------------
% 0.21/0.51  % (27904)Refutation not found, incomplete strategy% (27904)------------------------------
% 0.21/0.51  % (27904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27904)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (27904)Memory used [KB]: 10618
% 0.21/0.51  % (27904)Time elapsed: 0.063 s
% 0.21/0.51  % (27904)------------------------------
% 0.21/0.51  % (27904)------------------------------
% 0.21/0.51  % (27923)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (27922)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (27914)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (27917)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (27903)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (27914)Refutation not found, incomplete strategy% (27914)------------------------------
% 0.21/0.51  % (27914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27914)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (27914)Memory used [KB]: 10618
% 0.21/0.51  % (27914)Time elapsed: 0.108 s
% 0.21/0.51  % (27914)------------------------------
% 0.21/0.51  % (27914)------------------------------
% 0.21/0.51  % (27903)Refutation not found, incomplete strategy% (27903)------------------------------
% 0.21/0.51  % (27903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27903)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (27903)Memory used [KB]: 6140
% 0.21/0.51  % (27903)Time elapsed: 0.102 s
% 0.21/0.51  % (27903)------------------------------
% 0.21/0.51  % (27903)------------------------------
% 0.21/0.52  % (27923)Refutation not found, incomplete strategy% (27923)------------------------------
% 0.21/0.52  % (27923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27923)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27923)Memory used [KB]: 10618
% 0.21/0.52  % (27923)Time elapsed: 0.105 s
% 0.21/0.52  % (27923)------------------------------
% 0.21/0.52  % (27923)------------------------------
% 0.21/0.52  % (27910)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (27916)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f892,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f889,f494])).
% 0.21/0.52  fof(f494,plain,(
% 0.21/0.52    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f481])).
% 0.21/0.52  fof(f481,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.52    inference(backward_demodulation,[],[f10,f478])).
% 0.21/0.52  fof(f478,plain,(
% 0.21/0.52    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.52    inference(resolution,[],[f477,f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.52  fof(f477,plain,(
% 0.21/0.52    ( ! [X9] : (~v1_xboole_0(X9) | k5_relat_1(k1_xboole_0,sK0) = X9) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f475,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.52  fof(f475,plain,(
% 0.21/0.52    ( ! [X9] : (r2_hidden(sK6(X9),X9) | k5_relat_1(k1_xboole_0,sK0) = X9 | ~v1_xboole_0(X9)) )),
% 0.21/0.52    inference(resolution,[],[f464,f20])).
% 0.21/0.52  fof(f464,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,X0),sK2(k1_xboole_0,sK0,X0)),X0) | r2_hidden(sK6(X0),X0) | k5_relat_1(k1_xboole_0,sK0) = X0) )),
% 0.21/0.52    inference(resolution,[],[f462,f12])).
% 0.21/0.52  fof(f462,plain,(
% 0.21/0.52    ( ! [X15,X16] : (~v1_xboole_0(X15) | k5_relat_1(X15,sK0) = X16 | r2_hidden(sK6(X16),X16) | r2_hidden(k4_tarski(sK1(X15,sK0,X16),sK2(X15,sK0,X16)),X16)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f448,f20])).
% 0.21/0.52  fof(f448,plain,(
% 0.21/0.52    ( ! [X15,X16] : (r2_hidden(k4_tarski(sK1(X15,sK0,X16),sK2(X15,sK0,X16)),X16) | k5_relat_1(X15,sK0) = X16 | r2_hidden(sK6(X15),X15) | r2_hidden(sK6(X16),X16) | ~v1_xboole_0(X15)) )),
% 0.21/0.52    inference(resolution,[],[f238,f20])).
% 0.21/0.52  fof(f238,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(X0,sK0,X1),sK4(X0,sK0,X1)),X0) | r2_hidden(k4_tarski(sK1(X0,sK0,X1),sK2(X0,sK0,X1)),X1) | k5_relat_1(X0,sK0) = X1 | r2_hidden(sK6(X0),X0) | r2_hidden(sK6(X1),X1)) )),
% 0.21/0.52    inference(resolution,[],[f76,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK6(X0),X0) | v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X1,sK0,X0),sK4(X1,sK0,X0)),X1) | r2_hidden(k4_tarski(sK1(X1,sK0,X0),sK2(X1,sK0,X0)),X0) | k5_relat_1(X1,sK0) = X0 | r2_hidden(sK6(X1),X1)) )),
% 0.21/0.52    inference(resolution,[],[f31,f22])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X12,X11] : (~v1_relat_1(X11) | ~v1_relat_1(X12) | r2_hidden(k4_tarski(sK1(X11,sK0,X12),sK4(X11,sK0,X12)),X11) | r2_hidden(k4_tarski(sK1(X11,sK0,X12),sK2(X11,sK0,X12)),X12) | k5_relat_1(X11,sK0) = X12) )),
% 0.21/0.52    inference(resolution,[],[f11,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    v1_relat_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f5])).
% 0.21/0.52  fof(f5,conjecture,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f889,plain,(
% 0.21/0.52    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.52    inference(resolution,[],[f888,f12])).
% 0.21/0.52  fof(f888,plain,(
% 0.21/0.52    ( ! [X17] : (~v1_xboole_0(X17) | k5_relat_1(sK0,k1_xboole_0) = X17) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f877,f20])).
% 0.21/0.52  fof(f877,plain,(
% 0.21/0.52    ( ! [X17] : (r2_hidden(sK6(X17),X17) | k5_relat_1(sK0,k1_xboole_0) = X17 | ~v1_xboole_0(X17)) )),
% 0.21/0.52    inference(resolution,[],[f860,f20])).
% 0.21/0.52  fof(f860,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k4_tarski(sK1(sK0,k1_xboole_0,X0),sK2(sK0,k1_xboole_0,X0)),X0) | r2_hidden(sK6(X0),X0) | k5_relat_1(sK0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(resolution,[],[f858,f12])).
% 0.21/0.52  fof(f858,plain,(
% 0.21/0.52    ( ! [X30,X29] : (~v1_xboole_0(X29) | k5_relat_1(sK0,X29) = X30 | r2_hidden(sK6(X30),X30) | r2_hidden(k4_tarski(sK1(sK0,X29,X30),sK2(sK0,X29,X30)),X30)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f836,f20])).
% 0.21/0.52  fof(f836,plain,(
% 0.21/0.52    ( ! [X30,X29] : (r2_hidden(k4_tarski(sK1(sK0,X29,X30),sK2(sK0,X29,X30)),X30) | k5_relat_1(sK0,X29) = X30 | r2_hidden(sK6(X29),X29) | r2_hidden(sK6(X30),X30) | ~v1_xboole_0(X29)) )),
% 0.21/0.52    inference(resolution,[],[f271,f20])).
% 0.21/0.52  fof(f271,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(sK0,X0,X1),sK2(sK0,X0,X1)),X0) | r2_hidden(k4_tarski(sK1(sK0,X0,X1),sK2(sK0,X0,X1)),X1) | k5_relat_1(sK0,X0) = X1 | r2_hidden(sK6(X0),X0) | r2_hidden(sK6(X1),X1)) )),
% 0.21/0.52    inference(resolution,[],[f85,f22])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK4(sK0,X1,X0),sK2(sK0,X1,X0)),X1) | r2_hidden(k4_tarski(sK1(sK0,X1,X0),sK2(sK0,X1,X0)),X0) | k5_relat_1(sK0,X1) = X0 | r2_hidden(sK6(X1),X1)) )),
% 0.21/0.52    inference(resolution,[],[f33,f22])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X15,X16] : (~v1_relat_1(X15) | ~v1_relat_1(X16) | r2_hidden(k4_tarski(sK4(sK0,X15,X16),sK2(sK0,X15,X16)),X15) | r2_hidden(k4_tarski(sK1(sK0,X15,X16),sK2(sK0,X15,X16)),X16) | k5_relat_1(sK0,X15) = X16) )),
% 0.21/0.52    inference(resolution,[],[f11,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK2(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (27916)------------------------------
% 0.21/0.52  % (27916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27916)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (27916)Memory used [KB]: 2174
% 0.21/0.52  % (27916)Time elapsed: 0.091 s
% 0.21/0.52  % (27916)------------------------------
% 0.21/0.52  % (27916)------------------------------
% 0.21/0.52  % (27902)Success in time 0.159 s
%------------------------------------------------------------------------------

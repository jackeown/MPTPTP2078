%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:35 EST 2020

% Result     : Theorem 5.62s
% Output     : Refutation 5.62s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 288 expanded)
%              Number of leaves         :    8 (  71 expanded)
%              Depth                    :   17
%              Number of atoms          :  148 (2008 expanded)
%              Number of equality atoms :   30 ( 310 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6108,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f295,f326,f304,f74])).

fof(f74,plain,(
    ! [X6,X4,X5,X3] :
      ( r2_hidden(X6,k4_xboole_0(X3,k2_xboole_0(X4,X5)))
      | r2_hidden(X6,X5)
      | ~ r2_hidden(X6,k4_xboole_0(X3,X4)) ) ),
    inference(superposition,[],[f30,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f30,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).

fof(f16,plain,(
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

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f304,plain,(
    ! [X0] : ~ r2_hidden(sK2(X0,X0,k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) ),
    inference(forward_demodulation,[],[f294,f23])).

fof(f294,plain,(
    ! [X0] : ~ r2_hidden(sK2(X0,X0,k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f284,f42])).

fof(f42,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k3_xboole_0(X3,X4))
      | ~ r2_hidden(X5,k4_xboole_0(X3,X4)) ) ),
    inference(superposition,[],[f31,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f284,plain,(
    ! [X0] : r2_hidden(sK2(X0,X0,k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f35,f249])).

fof(f249,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK2(X2,X2,X3),X3)
      | k1_xboole_0 = X3 ) ),
    inference(backward_demodulation,[],[f143,f238])).

fof(f238,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f79,f143])).

fof(f79,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(condensation,[],[f76])).

fof(f76,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f70,f31])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f41,f33])).

fof(f33,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(unit_resulting_resolution,[],[f19,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f19,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f32,f20])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f143,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK2(X2,X2,X3),X3)
      | k4_xboole_0(X2,X2) = X3 ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X2) = X3
      | r2_hidden(sK2(X2,X2,X3),X3)
      | r2_hidden(sK2(X2,X2,X3),X3)
      | k4_xboole_0(X2,X2) = X3 ) ),
    inference(resolution,[],[f28,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    k1_xboole_0 != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f18,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f18,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
   => ~ r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

fof(f326,plain,(
    ! [X0,X1] : ~ r2_hidden(sK2(X0,X0,k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK1,X1)) ),
    inference(unit_resulting_resolution,[],[f308,f32])).

fof(f308,plain,(
    ! [X0] : ~ r2_hidden(sK2(X0,X0,k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK1) ),
    inference(unit_resulting_resolution,[],[f295,f31])).

fof(f295,plain,(
    ! [X0] : r2_hidden(sK2(X0,X0,k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f284,f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (21782)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (21782)Refutation not found, incomplete strategy% (21782)------------------------------
% 0.21/0.47  % (21782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (21782)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (21782)Memory used [KB]: 6140
% 0.21/0.47  % (21782)Time elapsed: 0.082 s
% 0.21/0.47  % (21782)------------------------------
% 0.21/0.47  % (21782)------------------------------
% 0.21/0.48  % (21800)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.48  % (21791)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (21800)Refutation not found, incomplete strategy% (21800)------------------------------
% 0.21/0.48  % (21800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21800)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21800)Memory used [KB]: 10618
% 0.21/0.48  % (21800)Time elapsed: 0.095 s
% 0.21/0.48  % (21800)------------------------------
% 0.21/0.48  % (21800)------------------------------
% 0.21/0.49  % (21784)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (21792)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (21783)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (21781)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (21809)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (21783)Refutation not found, incomplete strategy% (21783)------------------------------
% 0.21/0.51  % (21783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21783)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21783)Memory used [KB]: 6140
% 0.21/0.51  % (21783)Time elapsed: 0.104 s
% 0.21/0.51  % (21783)------------------------------
% 0.21/0.51  % (21783)------------------------------
% 0.21/0.51  % (21779)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (21780)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (21780)Refutation not found, incomplete strategy% (21780)------------------------------
% 0.21/0.52  % (21780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21780)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (21780)Memory used [KB]: 10618
% 0.21/0.52  % (21780)Time elapsed: 0.109 s
% 0.21/0.52  % (21780)------------------------------
% 0.21/0.52  % (21780)------------------------------
% 0.21/0.52  % (21778)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (21778)Refutation not found, incomplete strategy% (21778)------------------------------
% 0.21/0.52  % (21778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21778)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (21778)Memory used [KB]: 1663
% 0.21/0.52  % (21778)Time elapsed: 0.117 s
% 0.21/0.52  % (21778)------------------------------
% 0.21/0.52  % (21778)------------------------------
% 0.21/0.52  % (21799)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (21788)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (21808)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (21807)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (21802)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (21805)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (21787)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (21805)Refutation not found, incomplete strategy% (21805)------------------------------
% 0.21/0.53  % (21805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21805)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21805)Memory used [KB]: 6268
% 0.21/0.53  % (21805)Time elapsed: 0.127 s
% 0.21/0.53  % (21805)------------------------------
% 0.21/0.53  % (21805)------------------------------
% 0.21/0.54  % (21804)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (21789)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (21795)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (21795)Refutation not found, incomplete strategy% (21795)------------------------------
% 0.21/0.54  % (21795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21795)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21795)Memory used [KB]: 6140
% 0.21/0.54  % (21795)Time elapsed: 0.001 s
% 0.21/0.54  % (21795)------------------------------
% 0.21/0.54  % (21795)------------------------------
% 0.21/0.54  % (21789)Refutation not found, incomplete strategy% (21789)------------------------------
% 0.21/0.54  % (21789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21789)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21789)Memory used [KB]: 10618
% 0.21/0.54  % (21789)Time elapsed: 0.130 s
% 0.21/0.54  % (21789)------------------------------
% 0.21/0.54  % (21789)------------------------------
% 0.21/0.54  % (21785)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (21788)Refutation not found, incomplete strategy% (21788)------------------------------
% 0.21/0.54  % (21788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21788)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21788)Memory used [KB]: 10618
% 0.21/0.54  % (21788)Time elapsed: 0.139 s
% 0.21/0.54  % (21788)------------------------------
% 0.21/0.54  % (21788)------------------------------
% 0.21/0.54  % (21796)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (21801)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (21806)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (21803)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (21794)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (21798)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (21802)Refutation not found, incomplete strategy% (21802)------------------------------
% 0.21/0.55  % (21802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21802)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21802)Memory used [KB]: 10618
% 0.21/0.55  % (21802)Time elapsed: 0.142 s
% 0.21/0.55  % (21802)------------------------------
% 0.21/0.55  % (21802)------------------------------
% 0.21/0.55  % (21797)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (21797)Refutation not found, incomplete strategy% (21797)------------------------------
% 0.21/0.55  % (21797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21797)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21797)Memory used [KB]: 10618
% 0.21/0.55  % (21797)Time elapsed: 0.139 s
% 0.21/0.55  % (21797)------------------------------
% 0.21/0.55  % (21797)------------------------------
% 0.21/0.55  % (21801)Refutation not found, incomplete strategy% (21801)------------------------------
% 0.21/0.55  % (21801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21801)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21801)Memory used [KB]: 1663
% 0.21/0.55  % (21801)Time elapsed: 0.133 s
% 0.21/0.55  % (21801)------------------------------
% 0.21/0.55  % (21801)------------------------------
% 0.21/0.56  % (21787)Refutation not found, incomplete strategy% (21787)------------------------------
% 0.21/0.56  % (21787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (21787)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (21787)Memory used [KB]: 10618
% 0.21/0.56  % (21787)Time elapsed: 0.151 s
% 0.21/0.56  % (21787)------------------------------
% 0.21/0.56  % (21787)------------------------------
% 1.56/0.56  % (21790)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.56/0.57  % (21790)Refutation not found, incomplete strategy% (21790)------------------------------
% 1.56/0.57  % (21790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (21790)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (21790)Memory used [KB]: 10618
% 1.56/0.57  % (21790)Time elapsed: 0.172 s
% 1.56/0.57  % (21790)------------------------------
% 1.56/0.57  % (21790)------------------------------
% 1.75/0.62  % (21862)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.75/0.62  % (21862)Refutation not found, incomplete strategy% (21862)------------------------------
% 1.75/0.62  % (21862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.62  % (21862)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.62  
% 1.75/0.62  % (21862)Memory used [KB]: 6140
% 1.75/0.62  % (21862)Time elapsed: 0.121 s
% 1.75/0.62  % (21862)------------------------------
% 1.75/0.62  % (21862)------------------------------
% 1.75/0.62  % (21892)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.75/0.62  % (21872)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.09/0.64  % (21896)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.20/0.65  % (21917)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.20/0.66  % (21912)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.20/0.67  % (21912)Refutation not found, incomplete strategy% (21912)------------------------------
% 2.20/0.67  % (21912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.67  % (21912)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.67  
% 2.20/0.67  % (21912)Memory used [KB]: 1663
% 2.20/0.67  % (21912)Time elapsed: 0.097 s
% 2.20/0.67  % (21912)------------------------------
% 2.20/0.67  % (21912)------------------------------
% 2.20/0.67  % (21893)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.20/0.67  % (21779)Refutation not found, incomplete strategy% (21779)------------------------------
% 2.20/0.67  % (21779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.67  % (21907)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.20/0.68  % (21906)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.20/0.68  % (21921)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.20/0.68  % (21904)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.20/0.69  % (21779)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.69  
% 2.20/0.69  % (21779)Memory used [KB]: 6396
% 2.20/0.69  % (21779)Time elapsed: 0.260 s
% 2.20/0.69  % (21779)------------------------------
% 2.20/0.69  % (21779)------------------------------
% 2.20/0.69  % (21915)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.20/0.71  % (21919)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.64/0.72  % (21928)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 2.64/0.72  % (21939)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 2.64/0.73  % (21872)Refutation not found, incomplete strategy% (21872)------------------------------
% 2.64/0.73  % (21872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.73  % (21872)Termination reason: Refutation not found, incomplete strategy
% 2.64/0.73  
% 2.64/0.73  % (21872)Memory used [KB]: 6140
% 2.64/0.73  % (21872)Time elapsed: 0.210 s
% 2.64/0.73  % (21872)------------------------------
% 2.64/0.73  % (21872)------------------------------
% 2.64/0.73  % (21928)Refutation not found, incomplete strategy% (21928)------------------------------
% 2.64/0.73  % (21928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.73  % (21928)Termination reason: Refutation not found, incomplete strategy
% 2.64/0.73  
% 2.64/0.73  % (21928)Memory used [KB]: 1663
% 2.64/0.73  % (21928)Time elapsed: 0.135 s
% 2.64/0.73  % (21928)------------------------------
% 2.64/0.73  % (21928)------------------------------
% 3.05/0.80  % (21955)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 3.05/0.81  % (21950)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 3.05/0.83  % (21921)Refutation not found, incomplete strategy% (21921)------------------------------
% 3.05/0.83  % (21921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.05/0.83  % (21921)Termination reason: Refutation not found, incomplete strategy
% 3.05/0.83  
% 3.05/0.83  % (21921)Memory used [KB]: 1663
% 3.05/0.83  % (21921)Time elapsed: 0.260 s
% 3.05/0.83  % (21921)------------------------------
% 3.05/0.83  % (21921)------------------------------
% 3.05/0.84  % (21969)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 3.63/0.85  % (21969)Refutation not found, incomplete strategy% (21969)------------------------------
% 3.63/0.85  % (21969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/0.85  % (21969)Termination reason: Refutation not found, incomplete strategy
% 3.63/0.85  
% 3.63/0.85  % (21969)Memory used [KB]: 6140
% 3.63/0.85  % (21969)Time elapsed: 0.087 s
% 3.63/0.85  % (21969)------------------------------
% 3.63/0.85  % (21969)------------------------------
% 3.85/0.89  % (21791)Time limit reached!
% 3.85/0.89  % (21791)------------------------------
% 3.85/0.89  % (21791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.85/0.89  % (21791)Termination reason: Time limit
% 3.85/0.89  % (21791)Termination phase: Saturation
% 3.85/0.89  
% 3.85/0.89  % (21791)Memory used [KB]: 10874
% 3.85/0.89  % (21791)Time elapsed: 0.503 s
% 3.85/0.89  % (21791)------------------------------
% 3.85/0.89  % (21791)------------------------------
% 3.85/0.90  % (21974)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 4.22/0.95  % (22018)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 4.22/0.96  % (22013)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 4.22/0.97  % (21893)Time limit reached!
% 4.22/0.97  % (21893)------------------------------
% 4.22/0.97  % (21893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.22/0.97  % (21893)Termination reason: Time limit
% 4.22/0.97  
% 4.22/0.97  % (21893)Memory used [KB]: 8187
% 4.22/0.97  % (21893)Time elapsed: 0.413 s
% 4.22/0.97  % (21893)------------------------------
% 4.22/0.97  % (21893)------------------------------
% 4.22/0.97  % (21896)Time limit reached!
% 4.22/0.97  % (21896)------------------------------
% 4.22/0.97  % (21896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.22/0.97  % (21896)Termination reason: Time limit
% 4.22/0.97  
% 4.22/0.97  % (21896)Memory used [KB]: 13432
% 4.22/0.97  % (21896)Time elapsed: 0.426 s
% 4.22/0.97  % (21896)------------------------------
% 4.22/0.97  % (21896)------------------------------
% 4.63/1.01  % (21785)Time limit reached!
% 4.63/1.01  % (21785)------------------------------
% 4.63/1.01  % (21785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.01  % (21785)Termination reason: Time limit
% 4.63/1.01  
% 4.63/1.01  % (21785)Memory used [KB]: 11897
% 4.63/1.01  % (21785)Time elapsed: 0.602 s
% 4.63/1.01  % (21785)------------------------------
% 4.63/1.01  % (21785)------------------------------
% 4.63/1.02  % (22019)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 4.63/1.03  % (21796)Time limit reached!
% 4.63/1.03  % (21796)------------------------------
% 4.63/1.03  % (21796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.03  % (21796)Termination reason: Time limit
% 4.63/1.03  
% 4.63/1.03  % (21796)Memory used [KB]: 18038
% 4.63/1.03  % (21796)Time elapsed: 0.619 s
% 4.63/1.03  % (21796)------------------------------
% 4.63/1.03  % (21796)------------------------------
% 4.63/1.03  % (21808)Time limit reached!
% 4.63/1.03  % (21808)------------------------------
% 4.63/1.03  % (21808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.03  % (21808)Termination reason: Time limit
% 4.63/1.03  % (21808)Termination phase: Saturation
% 4.63/1.03  
% 4.63/1.03  % (21808)Memory used [KB]: 9338
% 4.63/1.03  % (21808)Time elapsed: 0.600 s
% 4.63/1.03  % (21808)------------------------------
% 4.63/1.03  % (21808)------------------------------
% 4.63/1.07  % (22020)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 5.62/1.10  % (21906)Refutation found. Thanks to Tanya!
% 5.62/1.10  % SZS status Theorem for theBenchmark
% 5.62/1.11  % (22021)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 5.62/1.12  % SZS output start Proof for theBenchmark
% 5.62/1.12  fof(f6108,plain,(
% 5.62/1.12    $false),
% 5.62/1.12    inference(unit_resulting_resolution,[],[f295,f326,f304,f74])).
% 5.62/1.12  fof(f74,plain,(
% 5.62/1.12    ( ! [X6,X4,X5,X3] : (r2_hidden(X6,k4_xboole_0(X3,k2_xboole_0(X4,X5))) | r2_hidden(X6,X5) | ~r2_hidden(X6,k4_xboole_0(X3,X4))) )),
% 5.62/1.12    inference(superposition,[],[f30,f23])).
% 5.62/1.12  fof(f23,plain,(
% 5.62/1.12    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 5.62/1.12    inference(cnf_transformation,[],[f4])).
% 5.62/1.12  fof(f4,axiom,(
% 5.62/1.12    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 5.62/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 5.62/1.12  fof(f30,plain,(
% 5.62/1.12    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 5.62/1.12    inference(equality_resolution,[],[f26])).
% 5.62/1.12  fof(f26,plain,(
% 5.62/1.12    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 5.62/1.12    inference(cnf_transformation,[],[f17])).
% 5.62/1.12  fof(f17,plain,(
% 5.62/1.12    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.62/1.12    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).
% 5.62/1.12  fof(f16,plain,(
% 5.62/1.12    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 5.62/1.12    introduced(choice_axiom,[])).
% 5.62/1.12  fof(f15,plain,(
% 5.62/1.12    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.62/1.12    inference(rectify,[],[f14])).
% 5.62/1.12  fof(f14,plain,(
% 5.62/1.12    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.62/1.12    inference(flattening,[],[f13])).
% 5.62/1.12  fof(f13,plain,(
% 5.62/1.12    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.62/1.12    inference(nnf_transformation,[],[f1])).
% 5.62/1.12  fof(f1,axiom,(
% 5.62/1.12    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 5.62/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 5.62/1.12  fof(f304,plain,(
% 5.62/1.12    ( ! [X0] : (~r2_hidden(sK2(X0,X0,k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK1,sK0))))) )),
% 5.62/1.12    inference(forward_demodulation,[],[f294,f23])).
% 5.62/1.12  fof(f294,plain,(
% 5.62/1.12    ( ! [X0] : (~r2_hidden(sK2(X0,X0,k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) )),
% 5.62/1.12    inference(unit_resulting_resolution,[],[f284,f42])).
% 5.62/1.12  fof(f42,plain,(
% 5.62/1.12    ( ! [X4,X5,X3] : (~r2_hidden(X5,k3_xboole_0(X3,X4)) | ~r2_hidden(X5,k4_xboole_0(X3,X4))) )),
% 5.62/1.12    inference(superposition,[],[f31,f20])).
% 5.62/1.12  fof(f20,plain,(
% 5.62/1.12    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.62/1.12    inference(cnf_transformation,[],[f5])).
% 5.62/1.12  fof(f5,axiom,(
% 5.62/1.12    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.62/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.62/1.12  fof(f31,plain,(
% 5.62/1.12    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 5.62/1.12    inference(equality_resolution,[],[f25])).
% 5.62/1.12  fof(f25,plain,(
% 5.62/1.12    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 5.62/1.12    inference(cnf_transformation,[],[f17])).
% 5.62/1.12  fof(f284,plain,(
% 5.62/1.12    ( ! [X0] : (r2_hidden(sK2(X0,X0,k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) )),
% 5.62/1.12    inference(unit_resulting_resolution,[],[f35,f249])).
% 5.62/1.12  fof(f249,plain,(
% 5.62/1.12    ( ! [X2,X3] : (r2_hidden(sK2(X2,X2,X3),X3) | k1_xboole_0 = X3) )),
% 5.62/1.12    inference(backward_demodulation,[],[f143,f238])).
% 5.62/1.12  fof(f238,plain,(
% 5.62/1.12    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 5.62/1.12    inference(unit_resulting_resolution,[],[f79,f143])).
% 5.62/1.12  fof(f79,plain,(
% 5.62/1.12    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 5.62/1.12    inference(condensation,[],[f76])).
% 5.62/1.12  fof(f76,plain,(
% 5.62/1.12    ( ! [X2,X3] : (~r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,X3)) )),
% 5.62/1.12    inference(resolution,[],[f70,f31])).
% 5.62/1.12  fof(f70,plain,(
% 5.62/1.12    ( ! [X2,X0,X1] : (r2_hidden(X2,k4_xboole_0(X0,X1)) | ~r2_hidden(X2,k1_xboole_0)) )),
% 5.62/1.12    inference(superposition,[],[f41,f33])).
% 5.62/1.12  fof(f33,plain,(
% 5.62/1.12    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 5.62/1.12    inference(unit_resulting_resolution,[],[f19,f21])).
% 5.62/1.12  fof(f21,plain,(
% 5.62/1.12    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 5.62/1.12    inference(cnf_transformation,[],[f12])).
% 5.62/1.12  fof(f12,plain,(
% 5.62/1.12    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 5.62/1.12    inference(nnf_transformation,[],[f2])).
% 5.62/1.12  fof(f2,axiom,(
% 5.62/1.12    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 5.62/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 5.62/1.12  fof(f19,plain,(
% 5.62/1.12    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 5.62/1.12    inference(cnf_transformation,[],[f6])).
% 5.62/1.12  fof(f6,axiom,(
% 5.62/1.12    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 5.62/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 5.62/1.12  fof(f41,plain,(
% 5.62/1.12    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | r2_hidden(X2,X0)) )),
% 5.62/1.12    inference(superposition,[],[f32,f20])).
% 5.62/1.12  fof(f32,plain,(
% 5.62/1.12    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 5.62/1.12    inference(equality_resolution,[],[f24])).
% 5.62/1.12  fof(f24,plain,(
% 5.62/1.12    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 5.62/1.12    inference(cnf_transformation,[],[f17])).
% 5.62/1.12  fof(f143,plain,(
% 5.62/1.12    ( ! [X2,X3] : (r2_hidden(sK2(X2,X2,X3),X3) | k4_xboole_0(X2,X2) = X3) )),
% 5.62/1.12    inference(duplicate_literal_removal,[],[f140])).
% 5.62/1.12  fof(f140,plain,(
% 5.62/1.12    ( ! [X2,X3] : (k4_xboole_0(X2,X2) = X3 | r2_hidden(sK2(X2,X2,X3),X3) | r2_hidden(sK2(X2,X2,X3),X3) | k4_xboole_0(X2,X2) = X3) )),
% 5.62/1.12    inference(resolution,[],[f28,f27])).
% 5.62/1.12  fof(f27,plain,(
% 5.62/1.12    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 5.62/1.12    inference(cnf_transformation,[],[f17])).
% 5.62/1.12  fof(f28,plain,(
% 5.62/1.12    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 5.62/1.12    inference(cnf_transformation,[],[f17])).
% 5.62/1.12  fof(f35,plain,(
% 5.62/1.12    k1_xboole_0 != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 5.62/1.12    inference(unit_resulting_resolution,[],[f18,f22])).
% 5.62/1.12  fof(f22,plain,(
% 5.62/1.12    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 5.62/1.12    inference(cnf_transformation,[],[f12])).
% 5.62/1.12  fof(f18,plain,(
% 5.62/1.12    ~r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 5.62/1.12    inference(cnf_transformation,[],[f11])).
% 5.62/1.12  fof(f11,plain,(
% 5.62/1.12    ~r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 5.62/1.12    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 5.62/1.12  fof(f10,plain,(
% 5.62/1.12    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) => ~r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 5.62/1.12    introduced(choice_axiom,[])).
% 5.62/1.12  fof(f9,plain,(
% 5.62/1.12    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 5.62/1.12    inference(ennf_transformation,[],[f8])).
% 5.62/1.12  fof(f8,negated_conjecture,(
% 5.62/1.12    ~! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 5.62/1.12    inference(negated_conjecture,[],[f7])).
% 5.62/1.12  fof(f7,conjecture,(
% 5.62/1.12    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 5.62/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).
% 5.62/1.12  fof(f326,plain,(
% 5.62/1.12    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X0,k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK1,X1))) )),
% 5.62/1.12    inference(unit_resulting_resolution,[],[f308,f32])).
% 5.62/1.12  fof(f308,plain,(
% 5.62/1.12    ( ! [X0] : (~r2_hidden(sK2(X0,X0,k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK1)) )),
% 5.62/1.12    inference(unit_resulting_resolution,[],[f295,f31])).
% 5.62/1.12  fof(f295,plain,(
% 5.62/1.12    ( ! [X0] : (r2_hidden(sK2(X0,X0,k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK0,sK1))) )),
% 5.62/1.12    inference(unit_resulting_resolution,[],[f284,f41])).
% 5.62/1.12  % SZS output end Proof for theBenchmark
% 5.62/1.12  % (21906)------------------------------
% 5.62/1.12  % (21906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.62/1.12  % (21906)Termination reason: Refutation
% 5.62/1.12  
% 5.62/1.12  % (21906)Memory used [KB]: 6012
% 5.62/1.12  % (21906)Time elapsed: 0.537 s
% 5.62/1.12  % (21906)------------------------------
% 5.62/1.12  % (21906)------------------------------
% 5.62/1.12  % (21775)Success in time 0.762 s
%------------------------------------------------------------------------------

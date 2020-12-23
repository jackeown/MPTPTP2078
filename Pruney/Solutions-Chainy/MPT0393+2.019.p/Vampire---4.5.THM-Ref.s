%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 222 expanded)
%              Number of leaves         :   13 (  58 expanded)
%              Depth                    :   20
%              Number of atoms          :  348 (1188 expanded)
%              Number of equality atoms :  180 ( 535 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f339,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f334])).

fof(f334,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f35,f284])).

fof(f284,plain,(
    ! [X9] : k1_setfam_1(k1_tarski(X9)) = X9 ),
    inference(subsumption_resolution,[],[f283,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(subsumption_resolution,[],[f85,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f85,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_tarski(X0)
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X0)) ) ),
    inference(superposition,[],[f76,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f76,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f283,plain,(
    ! [X9] :
      ( k1_setfam_1(k1_tarski(X9)) = X9
      | k1_xboole_0 = k1_tarski(X9) ) ),
    inference(subsumption_resolution,[],[f274,f82])).

fof(f82,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f80,f36])).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f80,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f274,plain,(
    ! [X9] :
      ( k1_setfam_1(k1_tarski(X9)) = X9
      | ~ r2_hidden(X9,k1_tarski(X9))
      | k1_xboole_0 = k1_tarski(X9) ) ),
    inference(duplicate_literal_removal,[],[f271])).

% (15853)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% (15854)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% (15861)Termination reason: Refutation not found, incomplete strategy

% (15861)Memory used [KB]: 6268
% (15861)Time elapsed: 0.098 s
% (15861)------------------------------
% (15861)------------------------------
% (15857)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (15877)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (15874)Refutation not found, incomplete strategy% (15874)------------------------------
% (15874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15874)Termination reason: Refutation not found, incomplete strategy

% (15874)Memory used [KB]: 10618
% (15874)Time elapsed: 0.144 s
% (15874)------------------------------
% (15874)------------------------------
% (15864)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (15864)Refutation not found, incomplete strategy% (15864)------------------------------
% (15864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15864)Termination reason: Refutation not found, incomplete strategy

% (15864)Memory used [KB]: 1663
% (15864)Time elapsed: 0.138 s
% (15864)------------------------------
% (15864)------------------------------
% (15863)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (15870)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (15876)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% (15876)Refutation not found, incomplete strategy% (15876)------------------------------
% (15876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15876)Termination reason: Refutation not found, incomplete strategy

% (15876)Memory used [KB]: 6140
% (15876)Time elapsed: 0.122 s
% (15876)------------------------------
% (15876)------------------------------
% (15871)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (15850)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f271,plain,(
    ! [X9] :
      ( k1_setfam_1(k1_tarski(X9)) = X9
      | ~ r2_hidden(X9,k1_tarski(X9))
      | k1_setfam_1(k1_tarski(X9)) = X9
      | ~ r2_hidden(X9,k1_tarski(X9))
      | k1_xboole_0 = k1_tarski(X9) ) ),
    inference(resolution,[],[f237,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | k1_setfam_1(X0) = X1
      | ~ r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(factoring,[],[f41])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK1(X0,X1),X4)
      | k1_setfam_1(X0) = X1
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
                  & r2_hidden(sK2(X0,X1),X0) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK1(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK3(X0,X5))
                    & r2_hidden(sK3(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f21,f20,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK1(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK1(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK1(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK3(X0,X5))
        & r2_hidden(sK3(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f237,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(k1_tarski(X0),X1),X0)
      | k1_setfam_1(k1_tarski(X0)) = X1
      | ~ r2_hidden(X1,k1_tarski(X0)) ) ),
    inference(subsumption_resolution,[],[f236,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_tarski(X1))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(subsumption_resolution,[],[f140,f86])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,k1_tarski(X1))
      | r2_hidden(X0,X2)
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f134,f71])).

fof(f71,plain,(
    ! [X0,X7,X5] :
      ( ~ r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X7,X0)
      | r2_hidden(X5,X7)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f134,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,k1_setfam_1(k1_tarski(X2)))
      | ~ r2_hidden(X3,X2) ) ),
    inference(subsumption_resolution,[],[f132,f86])).

fof(f132,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,X2)
      | r2_hidden(X3,k1_setfam_1(k1_tarski(X2)))
      | k1_xboole_0 = k1_tarski(X2) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,X2)
      | r2_hidden(X3,k1_setfam_1(k1_tarski(X2)))
      | k1_xboole_0 = k1_tarski(X2)
      | r2_hidden(X3,k1_setfam_1(k1_tarski(X2))) ) ),
    inference(superposition,[],[f69,f120])).

fof(f120,plain,(
    ! [X4,X5] :
      ( sK3(k1_tarski(X5),X4) = X5
      | r2_hidden(X4,k1_setfam_1(k1_tarski(X5))) ) ),
    inference(subsumption_resolution,[],[f119,f86])).

fof(f119,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,k1_setfam_1(k1_tarski(X5)))
      | k1_xboole_0 = k1_tarski(X5)
      | sK3(k1_tarski(X5),X4) = X5 ) ),
    inference(resolution,[],[f70,f107])).

fof(f107,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k1_tarski(X3))
      | X3 = X4 ) ),
    inference(trivial_inequality_removal,[],[f104])).

fof(f104,plain,(
    ! [X4,X3] :
      ( k1_tarski(X3) != k1_tarski(X3)
      | ~ r2_hidden(X4,k1_tarski(X3))
      | X3 = X4 ) ),
    inference(superposition,[],[f54,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f70,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK3(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,sK3(X0,X5))
      | r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK3(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(k1_tarski(X0),X1),X0)
      | k1_setfam_1(k1_tarski(X0)) = X1
      | ~ r2_hidden(sK1(k1_tarski(X0),X1),X1)
      | ~ r2_hidden(X1,k1_tarski(X0)) ) ),
    inference(subsumption_resolution,[],[f235,f86])).

fof(f235,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(k1_tarski(X0),X1),X0)
      | k1_setfam_1(k1_tarski(X0)) = X1
      | ~ r2_hidden(sK1(k1_tarski(X0),X1),X1)
      | k1_xboole_0 = k1_tarski(X0)
      | ~ r2_hidden(X1,k1_tarski(X0)) ) ),
    inference(duplicate_literal_removal,[],[f232])).

fof(f232,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(k1_tarski(X0),X1),X0)
      | k1_setfam_1(k1_tarski(X0)) = X1
      | ~ r2_hidden(sK1(k1_tarski(X0),X1),X1)
      | k1_xboole_0 = k1_tarski(X0)
      | k1_setfam_1(k1_tarski(X0)) = X1
      | ~ r2_hidden(X1,k1_tarski(X0)) ) ),
    inference(superposition,[],[f43,f223])).

fof(f223,plain,(
    ! [X4,X5] :
      ( sK2(k1_tarski(X4),X5) = X4
      | k1_setfam_1(k1_tarski(X4)) = X5
      | ~ r2_hidden(X5,k1_tarski(X4)) ) ),
    inference(subsumption_resolution,[],[f219,f86])).

fof(f219,plain,(
    ! [X4,X5] :
      ( k1_setfam_1(k1_tarski(X4)) = X5
      | sK2(k1_tarski(X4),X5) = X4
      | ~ r2_hidden(X5,k1_tarski(X4))
      | k1_xboole_0 = k1_tarski(X4) ) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,(
    ! [X4,X5] :
      ( k1_setfam_1(k1_tarski(X4)) = X5
      | sK2(k1_tarski(X4),X5) = X4
      | k1_setfam_1(k1_tarski(X4)) = X5
      | ~ r2_hidden(X5,k1_tarski(X4))
      | k1_xboole_0 = k1_tarski(X4) ) ),
    inference(resolution,[],[f139,f164])).

fof(f139,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK1(k1_tarski(X4),X5),X5)
      | k1_setfam_1(k1_tarski(X4)) = X5
      | sK2(k1_tarski(X4),X5) = X4 ) ),
    inference(subsumption_resolution,[],[f137,f86])).

fof(f137,plain,(
    ! [X4,X5] :
      ( k1_setfam_1(k1_tarski(X4)) = X5
      | ~ r2_hidden(sK1(k1_tarski(X4),X5),X5)
      | k1_xboole_0 = k1_tarski(X4)
      | sK2(k1_tarski(X4),X5) = X4 ) ),
    inference(resolution,[],[f42,f107])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_setfam_1(X0) = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
      | k1_setfam_1(X0) = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f15])).

fof(f15,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (15852)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (15860)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (15867)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  % (15867)Refutation not found, incomplete strategy% (15867)------------------------------
% 0.20/0.51  % (15867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (15867)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (15867)Memory used [KB]: 1663
% 0.20/0.51  % (15867)Time elapsed: 0.105 s
% 0.20/0.51  % (15867)------------------------------
% 0.20/0.51  % (15867)------------------------------
% 0.20/0.52  % (15851)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (15865)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (15859)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (15856)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (15874)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.52  % (15868)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (15868)Refutation not found, incomplete strategy% (15868)------------------------------
% 0.20/0.53  % (15868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (15868)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (15868)Memory used [KB]: 1663
% 0.20/0.53  % (15868)Time elapsed: 0.124 s
% 0.20/0.53  % (15868)------------------------------
% 0.20/0.53  % (15868)------------------------------
% 0.20/0.53  % (15851)Refutation not found, incomplete strategy% (15851)------------------------------
% 0.20/0.53  % (15851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (15851)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (15851)Memory used [KB]: 1663
% 0.20/0.53  % (15851)Time elapsed: 0.082 s
% 0.20/0.53  % (15851)------------------------------
% 0.20/0.53  % (15851)------------------------------
% 0.20/0.53  % (15855)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (15873)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (15861)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (15861)Refutation not found, incomplete strategy% (15861)------------------------------
% 0.20/0.53  % (15861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (15859)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f339,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f334])).
% 0.20/0.53  fof(f334,plain,(
% 0.20/0.53    sK0 != sK0),
% 0.20/0.53    inference(superposition,[],[f35,f284])).
% 0.20/0.53  fof(f284,plain,(
% 0.20/0.53    ( ! [X9] : (k1_setfam_1(k1_tarski(X9)) = X9) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f283,f86])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f85,f72])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(flattening,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0) | ~r1_tarski(k1_tarski(X0),k1_tarski(X0))) )),
% 0.20/0.53    inference(superposition,[],[f76,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.53    inference(nnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.20/0.53  fof(f283,plain,(
% 0.20/0.53    ( ! [X9] : (k1_setfam_1(k1_tarski(X9)) = X9 | k1_xboole_0 = k1_tarski(X9)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f274,f82])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.20/0.53    inference(superposition,[],[f80,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f79])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 0.20/0.53    inference(equality_resolution,[],[f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(rectify,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(flattening,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.53  fof(f274,plain,(
% 0.20/0.53    ( ! [X9] : (k1_setfam_1(k1_tarski(X9)) = X9 | ~r2_hidden(X9,k1_tarski(X9)) | k1_xboole_0 = k1_tarski(X9)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f271])).
% 0.20/0.53  % (15853)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (15854)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (15861)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (15861)Memory used [KB]: 6268
% 0.20/0.54  % (15861)Time elapsed: 0.098 s
% 0.20/0.54  % (15861)------------------------------
% 0.20/0.54  % (15861)------------------------------
% 0.20/0.54  % (15857)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (15877)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (15874)Refutation not found, incomplete strategy% (15874)------------------------------
% 0.20/0.54  % (15874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (15874)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (15874)Memory used [KB]: 10618
% 0.20/0.54  % (15874)Time elapsed: 0.144 s
% 0.20/0.54  % (15874)------------------------------
% 0.20/0.54  % (15874)------------------------------
% 0.20/0.55  % (15864)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.55  % (15864)Refutation not found, incomplete strategy% (15864)------------------------------
% 0.20/0.55  % (15864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (15864)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (15864)Memory used [KB]: 1663
% 0.20/0.55  % (15864)Time elapsed: 0.138 s
% 0.20/0.55  % (15864)------------------------------
% 0.20/0.55  % (15864)------------------------------
% 0.20/0.55  % (15863)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (15870)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (15876)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.59/0.55  % (15876)Refutation not found, incomplete strategy% (15876)------------------------------
% 1.59/0.55  % (15876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.55  % (15876)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.55  
% 1.59/0.55  % (15876)Memory used [KB]: 6140
% 1.59/0.55  % (15876)Time elapsed: 0.122 s
% 1.59/0.55  % (15876)------------------------------
% 1.59/0.55  % (15876)------------------------------
% 1.59/0.55  % (15871)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.59/0.55  % (15850)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.59/0.55  fof(f271,plain,(
% 1.59/0.55    ( ! [X9] : (k1_setfam_1(k1_tarski(X9)) = X9 | ~r2_hidden(X9,k1_tarski(X9)) | k1_setfam_1(k1_tarski(X9)) = X9 | ~r2_hidden(X9,k1_tarski(X9)) | k1_xboole_0 = k1_tarski(X9)) )),
% 1.59/0.55    inference(resolution,[],[f237,f164])).
% 1.59/0.55  fof(f164,plain,(
% 1.59/0.55    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | k1_setfam_1(X0) = X1 | ~r2_hidden(X1,X0) | k1_xboole_0 = X0) )),
% 1.59/0.55    inference(factoring,[],[f41])).
% 1.59/0.55  fof(f41,plain,(
% 1.59/0.55    ( ! [X4,X0,X1] : (r2_hidden(sK1(X0,X1),X4) | k1_setfam_1(X0) = X1 | ~r2_hidden(X4,X0) | r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 1.59/0.55    inference(cnf_transformation,[],[f22])).
% 1.59/0.55  fof(f22,plain,(
% 1.59/0.55    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | ~r2_hidden(sK1(X0,X1),X1)) & (! [X4] : (r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK3(X0,X5)) & r2_hidden(sK3(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 1.59/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f21,f20,f19])).
% 1.59/0.55  fof(f19,plain,(
% 1.59/0.55    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK1(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK1(X0,X1),X1)) & (! [X4] : (r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK1(X0,X1),X1))))),
% 1.59/0.55    introduced(choice_axiom,[])).
% 1.59/0.55  fof(f20,plain,(
% 1.59/0.55    ! [X1,X0] : (? [X3] : (~r2_hidden(sK1(X0,X1),X3) & r2_hidden(X3,X0)) => (~r2_hidden(sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 1.59/0.55    introduced(choice_axiom,[])).
% 1.59/0.55  fof(f21,plain,(
% 1.59/0.55    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK3(X0,X5)) & r2_hidden(sK3(X0,X5),X0)))),
% 1.59/0.55    introduced(choice_axiom,[])).
% 1.59/0.55  fof(f18,plain,(
% 1.59/0.55    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 1.59/0.55    inference(rectify,[],[f17])).
% 1.59/0.55  fof(f17,plain,(
% 1.59/0.55    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 1.59/0.55    inference(nnf_transformation,[],[f14])).
% 1.59/0.55  fof(f14,plain,(
% 1.59/0.55    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 1.59/0.55    inference(ennf_transformation,[],[f10])).
% 1.59/0.55  fof(f10,axiom,(
% 1.59/0.55    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 1.59/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).
% 1.59/0.55  fof(f237,plain,(
% 1.59/0.55    ( ! [X0,X1] : (~r2_hidden(sK1(k1_tarski(X0),X1),X0) | k1_setfam_1(k1_tarski(X0)) = X1 | ~r2_hidden(X1,k1_tarski(X0))) )),
% 1.59/0.55    inference(subsumption_resolution,[],[f236,f141])).
% 1.59/0.55  fof(f141,plain,(
% 1.59/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_tarski(X1)) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.59/0.55    inference(subsumption_resolution,[],[f140,f86])).
% 1.59/0.55  fof(f140,plain,(
% 1.59/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,k1_tarski(X1)) | r2_hidden(X0,X2) | k1_xboole_0 = k1_tarski(X1)) )),
% 1.59/0.55    inference(resolution,[],[f134,f71])).
% 1.59/0.55  fof(f71,plain,(
% 1.59/0.55    ( ! [X0,X7,X5] : (~r2_hidden(X5,k1_setfam_1(X0)) | ~r2_hidden(X7,X0) | r2_hidden(X5,X7) | k1_xboole_0 = X0) )),
% 1.59/0.55    inference(equality_resolution,[],[f38])).
% 1.59/0.55  fof(f38,plain,(
% 1.59/0.55    ( ! [X0,X7,X5,X1] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,X1) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 1.59/0.55    inference(cnf_transformation,[],[f22])).
% 1.59/0.55  fof(f134,plain,(
% 1.59/0.55    ( ! [X2,X3] : (r2_hidden(X3,k1_setfam_1(k1_tarski(X2))) | ~r2_hidden(X3,X2)) )),
% 1.59/0.55    inference(subsumption_resolution,[],[f132,f86])).
% 1.59/0.55  fof(f132,plain,(
% 1.59/0.55    ( ! [X2,X3] : (~r2_hidden(X3,X2) | r2_hidden(X3,k1_setfam_1(k1_tarski(X2))) | k1_xboole_0 = k1_tarski(X2)) )),
% 1.59/0.55    inference(duplicate_literal_removal,[],[f131])).
% 1.59/0.55  fof(f131,plain,(
% 1.59/0.55    ( ! [X2,X3] : (~r2_hidden(X3,X2) | r2_hidden(X3,k1_setfam_1(k1_tarski(X2))) | k1_xboole_0 = k1_tarski(X2) | r2_hidden(X3,k1_setfam_1(k1_tarski(X2)))) )),
% 1.59/0.55    inference(superposition,[],[f69,f120])).
% 1.59/0.55  fof(f120,plain,(
% 1.59/0.55    ( ! [X4,X5] : (sK3(k1_tarski(X5),X4) = X5 | r2_hidden(X4,k1_setfam_1(k1_tarski(X5)))) )),
% 1.59/0.55    inference(subsumption_resolution,[],[f119,f86])).
% 1.59/0.55  fof(f119,plain,(
% 1.59/0.55    ( ! [X4,X5] : (r2_hidden(X4,k1_setfam_1(k1_tarski(X5))) | k1_xboole_0 = k1_tarski(X5) | sK3(k1_tarski(X5),X4) = X5) )),
% 1.59/0.55    inference(resolution,[],[f70,f107])).
% 1.59/0.55  fof(f107,plain,(
% 1.59/0.55    ( ! [X4,X3] : (~r2_hidden(X4,k1_tarski(X3)) | X3 = X4) )),
% 1.59/0.55    inference(trivial_inequality_removal,[],[f104])).
% 1.59/0.55  fof(f104,plain,(
% 1.59/0.55    ( ! [X4,X3] : (k1_tarski(X3) != k1_tarski(X3) | ~r2_hidden(X4,k1_tarski(X3)) | X3 = X4) )),
% 1.59/0.55    inference(superposition,[],[f54,f57])).
% 1.59/0.55  fof(f57,plain,(
% 1.59/0.55    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.59/0.55    inference(cnf_transformation,[],[f29])).
% 1.59/0.55  fof(f54,plain,(
% 1.59/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.59/0.55    inference(cnf_transformation,[],[f28])).
% 1.59/0.55  fof(f28,plain,(
% 1.59/0.55    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.59/0.55    inference(nnf_transformation,[],[f9])).
% 1.59/0.55  fof(f9,axiom,(
% 1.59/0.55    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.59/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.59/0.55  fof(f70,plain,(
% 1.59/0.55    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),X0) | r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 1.59/0.55    inference(equality_resolution,[],[f39])).
% 1.59/0.55  fof(f39,plain,(
% 1.59/0.55    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | r2_hidden(sK3(X0,X5),X0) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 1.59/0.55    inference(cnf_transformation,[],[f22])).
% 1.59/0.55  fof(f69,plain,(
% 1.59/0.55    ( ! [X0,X5] : (~r2_hidden(X5,sK3(X0,X5)) | r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 1.59/0.55    inference(equality_resolution,[],[f40])).
% 1.59/0.55  fof(f40,plain,(
% 1.59/0.55    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X5,sK3(X0,X5)) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 1.59/0.55    inference(cnf_transformation,[],[f22])).
% 1.59/0.55  fof(f236,plain,(
% 1.59/0.55    ( ! [X0,X1] : (~r2_hidden(sK1(k1_tarski(X0),X1),X0) | k1_setfam_1(k1_tarski(X0)) = X1 | ~r2_hidden(sK1(k1_tarski(X0),X1),X1) | ~r2_hidden(X1,k1_tarski(X0))) )),
% 1.59/0.55    inference(subsumption_resolution,[],[f235,f86])).
% 1.59/0.55  fof(f235,plain,(
% 1.59/0.55    ( ! [X0,X1] : (~r2_hidden(sK1(k1_tarski(X0),X1),X0) | k1_setfam_1(k1_tarski(X0)) = X1 | ~r2_hidden(sK1(k1_tarski(X0),X1),X1) | k1_xboole_0 = k1_tarski(X0) | ~r2_hidden(X1,k1_tarski(X0))) )),
% 1.59/0.55    inference(duplicate_literal_removal,[],[f232])).
% 1.59/0.55  fof(f232,plain,(
% 1.59/0.55    ( ! [X0,X1] : (~r2_hidden(sK1(k1_tarski(X0),X1),X0) | k1_setfam_1(k1_tarski(X0)) = X1 | ~r2_hidden(sK1(k1_tarski(X0),X1),X1) | k1_xboole_0 = k1_tarski(X0) | k1_setfam_1(k1_tarski(X0)) = X1 | ~r2_hidden(X1,k1_tarski(X0))) )),
% 1.59/0.55    inference(superposition,[],[f43,f223])).
% 1.59/0.55  fof(f223,plain,(
% 1.59/0.55    ( ! [X4,X5] : (sK2(k1_tarski(X4),X5) = X4 | k1_setfam_1(k1_tarski(X4)) = X5 | ~r2_hidden(X5,k1_tarski(X4))) )),
% 1.59/0.55    inference(subsumption_resolution,[],[f219,f86])).
% 1.59/0.55  fof(f219,plain,(
% 1.59/0.55    ( ! [X4,X5] : (k1_setfam_1(k1_tarski(X4)) = X5 | sK2(k1_tarski(X4),X5) = X4 | ~r2_hidden(X5,k1_tarski(X4)) | k1_xboole_0 = k1_tarski(X4)) )),
% 1.59/0.55    inference(duplicate_literal_removal,[],[f216])).
% 1.59/0.55  fof(f216,plain,(
% 1.59/0.55    ( ! [X4,X5] : (k1_setfam_1(k1_tarski(X4)) = X5 | sK2(k1_tarski(X4),X5) = X4 | k1_setfam_1(k1_tarski(X4)) = X5 | ~r2_hidden(X5,k1_tarski(X4)) | k1_xboole_0 = k1_tarski(X4)) )),
% 1.59/0.55    inference(resolution,[],[f139,f164])).
% 1.59/0.55  fof(f139,plain,(
% 1.59/0.55    ( ! [X4,X5] : (~r2_hidden(sK1(k1_tarski(X4),X5),X5) | k1_setfam_1(k1_tarski(X4)) = X5 | sK2(k1_tarski(X4),X5) = X4) )),
% 1.59/0.55    inference(subsumption_resolution,[],[f137,f86])).
% 1.59/0.55  fof(f137,plain,(
% 1.59/0.55    ( ! [X4,X5] : (k1_setfam_1(k1_tarski(X4)) = X5 | ~r2_hidden(sK1(k1_tarski(X4),X5),X5) | k1_xboole_0 = k1_tarski(X4) | sK2(k1_tarski(X4),X5) = X4) )),
% 1.59/0.55    inference(resolution,[],[f42,f107])).
% 1.59/0.55  fof(f42,plain,(
% 1.59/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_setfam_1(X0) = X1 | ~r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 1.59/0.55    inference(cnf_transformation,[],[f22])).
% 1.59/0.55  fof(f43,plain,(
% 1.59/0.55    ( ! [X0,X1] : (~r2_hidden(sK1(X0,X1),sK2(X0,X1)) | k1_setfam_1(X0) = X1 | ~r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 1.59/0.55    inference(cnf_transformation,[],[f22])).
% 1.59/0.55  fof(f35,plain,(
% 1.59/0.55    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 1.59/0.55    inference(cnf_transformation,[],[f16])).
% 1.59/0.55  fof(f16,plain,(
% 1.59/0.55    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 1.59/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f15])).
% 1.59/0.55  fof(f15,plain,(
% 1.59/0.55    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => sK0 != k1_setfam_1(k1_tarski(sK0))),
% 1.59/0.55    introduced(choice_axiom,[])).
% 1.59/0.55  fof(f13,plain,(
% 1.59/0.55    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 1.59/0.55    inference(ennf_transformation,[],[f12])).
% 1.59/0.55  fof(f12,negated_conjecture,(
% 1.59/0.55    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.59/0.55    inference(negated_conjecture,[],[f11])).
% 1.59/0.55  fof(f11,conjecture,(
% 1.59/0.55    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.59/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.59/0.55  % SZS output end Proof for theBenchmark
% 1.59/0.55  % (15859)------------------------------
% 1.59/0.55  % (15859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.55  % (15859)Termination reason: Refutation
% 1.59/0.55  
% 1.59/0.55  % (15859)Memory used [KB]: 1918
% 1.59/0.55  % (15859)Time elapsed: 0.127 s
% 1.59/0.55  % (15859)------------------------------
% 1.59/0.55  % (15859)------------------------------
% 1.59/0.55  % (15875)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.59/0.56  % (15849)Success in time 0.199 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0254+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:19 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 291 expanded)
%              Number of leaves         :   17 (  86 expanded)
%              Depth                    :   16
%              Number of atoms          :  159 ( 428 expanded)
%              Number of equality atoms :   40 ( 280 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1236,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1224,f1235])).

fof(f1235,plain,(
    ! [X23] : ~ r2_hidden(X23,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1230,f732])).

fof(f732,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f541])).

fof(f541,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X0)
        & r2_hidden(X1,X2) )
      | ~ sP6(X0,X1,X2) ) ),
    inference(rectify,[],[f540])).

fof(f540,plain,(
    ! [X1,X2,X0] :
      ( ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ sP6(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f480])).

fof(f480,plain,(
    ! [X1,X2,X0] :
      ( ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ sP6(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f1230,plain,(
    ! [X23] :
      ( sP6(k1_xboole_0,X23,k1_xboole_0)
      | ~ r2_hidden(X23,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f1112,f1221])).

fof(f1221,plain,(
    k1_xboole_0 = sK16 ),
    inference(forward_demodulation,[],[f1220,f1084])).

fof(f1084,plain,(
    ! [X2] : k2_xboole_0(X2,sK16) = X2 ),
    inference(forward_demodulation,[],[f1083,f647])).

fof(f647,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f1083,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(X2,k1_xboole_0),sK16) = X2 ),
    inference(forward_demodulation,[],[f1082,f985])).

fof(f985,plain,(
    k1_xboole_0 = k2_tarski(sK15,sK15) ),
    inference(unit_resulting_resolution,[],[f848,f640])).

fof(f640,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f373])).

fof(f373,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f71])).

fof(f71,axiom,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k1_xboole_0
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

fof(f848,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK15,sK15),sK16) ),
    inference(definition_unfolding,[],[f590,f726])).

fof(f726,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f590,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK15),sK16) ),
    inference(cnf_transformation,[],[f496])).

fof(f496,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK15),sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f359,f495])).

fof(f495,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK15),sK16) ),
    introduced(choice_axiom,[])).

fof(f359,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f351])).

fof(f351,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f350])).

fof(f350,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f1082,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(X2,k2_tarski(sK15,sK15)),sK16) = X2 ),
    inference(forward_demodulation,[],[f1081,f647])).

fof(f1081,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(X2,k2_tarski(sK15,sK15)),sK16) = k2_xboole_0(X2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1080,f1072])).

fof(f1072,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK16) ),
    inference(backward_demodulation,[],[f848,f985])).

fof(f1080,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(X2,k2_tarski(sK15,sK15)),sK16) = k2_xboole_0(X2,k2_xboole_0(k1_xboole_0,sK16)) ),
    inference(forward_demodulation,[],[f1079,f595])).

fof(f595,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1079,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(X2,k2_tarski(sK15,sK15)),sK16) = k2_xboole_0(X2,k2_xboole_0(sK16,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1021,f593])).

fof(f593,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1021,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(X2,k2_tarski(sK15,sK15)),sK16) = k2_xboole_0(k2_xboole_0(X2,sK16),k1_xboole_0) ),
    inference(superposition,[],[f592,f848])).

fof(f592,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f125])).

fof(f125,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_1)).

fof(f1220,plain,(
    sK16 = k2_xboole_0(k1_xboole_0,sK16) ),
    inference(forward_demodulation,[],[f1187,f985])).

fof(f1187,plain,(
    sK16 = k2_xboole_0(k2_tarski(sK15,sK15),sK16) ),
    inference(unit_resulting_resolution,[],[f1075,f935])).

fof(f935,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_tarski(X0,X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f821,f726])).

fof(f821,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f456])).

fof(f456,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f296])).

% (30958)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
% (30943)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
% (30962)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_157 on theBenchmark
% (30943)Refutation not found, incomplete strategy% (30943)------------------------------
% (30943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30943)Termination reason: Refutation not found, incomplete strategy

% (30943)Memory used [KB]: 6396
% (30943)Time elapsed: 0.004 s
% (30943)------------------------------
% (30943)------------------------------
% (30954)dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_4 on theBenchmark
% (30959)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% (30964)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (30969)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_48 on theBenchmark
% (30967)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% (30951)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% (30964)Refutation not found, incomplete strategy% (30964)------------------------------
% (30964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30964)Termination reason: Refutation not found, incomplete strategy

% (30964)Memory used [KB]: 11257
% (30964)Time elapsed: 0.113 s
% (30964)------------------------------
% (30964)------------------------------
% (30957)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
% (30961)ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=input_only:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_70 on theBenchmark
% (30966)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
% (30946)dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_17 on theBenchmark
fof(f296,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f1075,plain,(
    r2_hidden(sK15,sK16) ),
    inference(subsumption_resolution,[],[f1014,f651])).

fof(f651,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1014,plain,
    ( ~ r1_tarski(k1_xboole_0,sK16)
    | r2_hidden(sK15,sK16) ),
    inference(superposition,[],[f715,f848])).

fof(f715,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(cnf_transformation,[],[f404])).

fof(f404,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f348])).

fof(f348,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f1112,plain,(
    ! [X23] :
      ( sP6(sK16,X23,k1_xboole_0)
      | ~ r2_hidden(X23,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f1103,f1111])).

fof(f1111,plain,(
    ! [X31] : r1_xboole_0(X31,sK16) ),
    inference(subsumption_resolution,[],[f1053,f652])).

fof(f652,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f1053,plain,(
    ! [X31] :
      ( ~ r1_xboole_0(X31,k1_xboole_0)
      | r1_xboole_0(X31,sK16) ) ),
    inference(superposition,[],[f751,f848])).

fof(f751,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f435])).

fof(f435,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f138])).

fof(f138,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f1103,plain,(
    ! [X23] :
      ( ~ r1_xboole_0(k1_xboole_0,sK16)
      | sP6(sK16,X23,k1_xboole_0)
      | ~ r2_hidden(X23,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f1102,f763])).

fof(f763,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f544])).

fof(f544,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK22(X0,X1),X1)
          & r2_hidden(sK22(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f443,f543])).

fof(f543,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK22(X0,X1),X1)
        & r2_hidden(sK22(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f443,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f356])).

fof(f356,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1102,plain,(
    ! [X23] :
      ( ~ r1_xboole_0(k1_xboole_0,sK16)
      | sP6(sK16,X23,k1_xboole_0)
      | ~ r2_hidden(X23,k1_xboole_0)
      | r2_hidden(X23,sK16) ) ),
    inference(forward_demodulation,[],[f1101,f985])).

fof(f1101,plain,(
    ! [X23] :
      ( sP6(sK16,X23,k1_xboole_0)
      | ~ r2_hidden(X23,k1_xboole_0)
      | r2_hidden(X23,sK16)
      | ~ r1_xboole_0(k2_tarski(sK15,sK15),sK16) ) ),
    inference(forward_demodulation,[],[f1045,f985])).

fof(f1045,plain,(
    ! [X23] :
      ( ~ r2_hidden(X23,k1_xboole_0)
      | r2_hidden(X23,sK16)
      | sP6(sK16,X23,k2_tarski(sK15,sK15))
      | ~ r1_xboole_0(k2_tarski(sK15,sK15),sK16) ) ),
    inference(superposition,[],[f733,f848])).

fof(f733,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | sP6(X1,X2,X0)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f481])).

fof(f481,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | sP6(X1,X2,X0)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_folding,[],[f417,f480])).

fof(f417,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).

fof(f1224,plain,(
    r2_hidden(sK15,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1075,f1221])).
%------------------------------------------------------------------------------

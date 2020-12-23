%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0268+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:20 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 107 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :   70
%              Number of atoms          :  131 ( 198 expanded)
%              Number of equality atoms :   25 (  54 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1279,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1273,f1157])).

fof(f1157,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(duplicate_literal_removal,[],[f1076])).

fof(f1076,plain,
    ( ~ r2_hidden(sK16,sK15)
    | ~ r2_hidden(sK16,sK15) ),
    inference(superposition,[],[f1037,f619])).

fof(f619,plain,
    ( sK15 = k4_xboole_0(sK15,k1_tarski(sK16))
    | ~ r2_hidden(sK16,sK15) ),
    inference(cnf_transformation,[],[f523])).

fof(f523,plain,
    ( ( r2_hidden(sK16,sK15)
      | sK15 != k4_xboole_0(sK15,k1_tarski(sK16)) )
    & ( ~ r2_hidden(sK16,sK15)
      | sK15 = k4_xboole_0(sK15,k1_tarski(sK16)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f521,f522])).

fof(f522,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK16,sK15)
        | sK15 != k4_xboole_0(sK15,k1_tarski(sK16)) )
      & ( ~ r2_hidden(sK16,sK15)
        | sK15 = k4_xboole_0(sK15,k1_tarski(sK16)) ) ) ),
    introduced(choice_axiom,[])).

fof(f521,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f373])).

fof(f373,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f365])).

fof(f365,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f364])).

fof(f364,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f1037,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f635])).

fof(f635,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f531])).

fof(f531,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f530])).

fof(f530,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f363])).

fof(f363,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f1273,plain,(
    r2_hidden(sK16,sK15) ),
    inference(resolution,[],[f1269,f719])).

fof(f719,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f406])).

fof(f406,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f298])).

fof(f298,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f1269,plain,(
    ~ r1_xboole_0(k1_tarski(sK16),sK15) ),
    inference(resolution,[],[f1267,f843])).

fof(f843,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f475])).

fof(f475,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1267,plain,(
    ~ r1_xboole_0(sK15,k1_tarski(sK16)) ),
    inference(trivial_inequality_removal,[],[f1265])).

fof(f1265,plain,
    ( sK15 != sK15
    | ~ r1_xboole_0(sK15,k1_tarski(sK16)) ),
    inference(superposition,[],[f1260,f752])).

fof(f752,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f593])).

fof(f593,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f153])).

fof(f153,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f1260,plain,(
    sK15 != k4_xboole_0(sK15,k1_tarski(sK16)) ),
    inference(global_subsumption,[],[f1259,f620])).

fof(f620,plain,
    ( r2_hidden(sK16,sK15)
    | sK15 != k4_xboole_0(sK15,k1_tarski(sK16)) ),
    inference(cnf_transformation,[],[f523])).

fof(f1259,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1258])).

fof(f1258,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1257])).

fof(f1257,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1256])).

fof(f1256,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1254])).

fof(f1254,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1253])).

fof(f1253,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1252])).

fof(f1252,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1251])).

% (32291)Refutation not found, incomplete strategy% (32291)------------------------------
% (32291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32291)Termination reason: Refutation not found, incomplete strategy

% (32291)Memory used [KB]: 11385
% (32291)Time elapsed: 0.100 s
% (32291)------------------------------
% (32291)------------------------------
fof(f1251,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1247])).

fof(f1247,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1244])).

fof(f1244,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1242])).

fof(f1242,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1237])).

fof(f1237,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1233])).

fof(f1233,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1230])).

fof(f1230,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1228])).

fof(f1228,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1227])).

fof(f1227,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1226])).

fof(f1226,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1225])).

fof(f1225,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1224])).

fof(f1224,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1223])).

% (32285)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
fof(f1223,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1222])).

fof(f1222,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1221])).

fof(f1221,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1220])).

fof(f1220,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1219])).

fof(f1219,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1215])).

fof(f1215,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1213])).

fof(f1213,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1210])).

fof(f1210,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1208])).

fof(f1208,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1205])).

fof(f1205,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1204])).

fof(f1204,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1203])).

% (32286)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
fof(f1203,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1202])).

fof(f1202,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1200])).

fof(f1200,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1197])).

fof(f1197,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1195])).

fof(f1195,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1191])).

% (32284)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
fof(f1191,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1184])).

fof(f1184,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1182])).

fof(f1182,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1181])).

fof(f1181,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1180])).

fof(f1180,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1178])).

fof(f1178,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1177])).

fof(f1177,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1176])).

fof(f1176,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1175])).

fof(f1175,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1174])).

fof(f1174,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1173])).

fof(f1173,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1172])).

fof(f1172,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1171])).

fof(f1171,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1170])).

fof(f1170,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1168])).

fof(f1168,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1167])).

fof(f1167,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1166])).

fof(f1166,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1164])).

fof(f1164,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1163])).

fof(f1163,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1162])).

fof(f1162,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1161])).

fof(f1161,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1160])).

fof(f1160,plain,(
    ~ r2_hidden(sK16,sK15) ),
    inference(global_subsumption,[],[f1157])).
%------------------------------------------------------------------------------

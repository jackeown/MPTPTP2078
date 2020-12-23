%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0761+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   84 (2981 expanded)
%              Number of leaves         :    8 ( 787 expanded)
%              Depth                    :   47
%              Number of atoms          :  352 (16328 expanded)
%              Number of equality atoms :   77 (1834 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1269,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1268,f1159])).

fof(f1159,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1148])).

fof(f1148,plain,
    ( ( ~ r1_wellord1(sK0,k3_relat_1(sK0))
      | ~ v1_wellord1(sK0) )
    & ( r1_wellord1(sK0,k3_relat_1(sK0))
      | v1_wellord1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1146,f1147])).

fof(f1147,plain,
    ( ? [X0] :
        ( ( ~ r1_wellord1(X0,k3_relat_1(X0))
          | ~ v1_wellord1(X0) )
        & ( r1_wellord1(X0,k3_relat_1(X0))
          | v1_wellord1(X0) )
        & v1_relat_1(X0) )
   => ( ( ~ r1_wellord1(sK0,k3_relat_1(sK0))
        | ~ v1_wellord1(sK0) )
      & ( r1_wellord1(sK0,k3_relat_1(sK0))
        | v1_wellord1(sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1146,plain,(
    ? [X0] :
      ( ( ~ r1_wellord1(X0,k3_relat_1(X0))
        | ~ v1_wellord1(X0) )
      & ( r1_wellord1(X0,k3_relat_1(X0))
        | v1_wellord1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1145])).

fof(f1145,plain,(
    ? [X0] :
      ( ( ~ r1_wellord1(X0,k3_relat_1(X0))
        | ~ v1_wellord1(X0) )
      & ( r1_wellord1(X0,k3_relat_1(X0))
        | v1_wellord1(X0) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1134])).

fof(f1134,plain,(
    ? [X0] :
      ( ( v1_wellord1(X0)
      <~> r1_wellord1(X0,k3_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1133])).

fof(f1133,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v1_wellord1(X0)
        <=> r1_wellord1(X0,k3_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f1132])).

fof(f1132,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord1)).

fof(f1268,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1263,f1237])).

fof(f1237,plain,(
    ~ r1_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f1161,f1236])).

fof(f1236,plain,(
    v1_wellord1(sK0) ),
    inference(subsumption_resolution,[],[f1234,f1159])).

fof(f1234,plain,
    ( v1_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f1233])).

fof(f1233,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f1180,f1230])).

fof(f1230,plain,(
    k1_xboole_0 = sK3(sK0) ),
    inference(subsumption_resolution,[],[f1229,f1206])).

fof(f1206,plain,
    ( ~ r1_wellord1(sK0,k3_relat_1(sK0))
    | k1_xboole_0 = sK3(sK0) ),
    inference(resolution,[],[f1203,f1161])).

fof(f1203,plain,
    ( v1_wellord1(sK0)
    | k1_xboole_0 = sK3(sK0) ),
    inference(subsumption_resolution,[],[f1202,f1183])).

fof(f1183,plain,
    ( r1_tarski(sK3(sK0),k3_relat_1(sK0))
    | v1_wellord1(sK0) ),
    inference(resolution,[],[f1179,f1159])).

fof(f1179,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(sK3(X0),k3_relat_1(X0))
      | v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f1158])).

fof(f1158,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ( ! [X2] :
                ( ~ r1_xboole_0(k1_wellord1(X0,X2),sK3(X0))
                | ~ r2_hidden(X2,sK3(X0)) )
            & k1_xboole_0 != sK3(X0)
            & r1_tarski(sK3(X0),k3_relat_1(X0)) ) )
        & ( ! [X3] :
              ( ( r1_xboole_0(k1_wellord1(X0,sK4(X0,X3)),X3)
                & r2_hidden(sK4(X0,X3),X3) )
              | k1_xboole_0 = X3
              | ~ r1_tarski(X3,k3_relat_1(X0)) )
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f1155,f1157,f1156])).

fof(f1156,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r1_xboole_0(k1_wellord1(X0,X2),X1)
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
     => ( ! [X2] :
            ( ~ r1_xboole_0(k1_wellord1(X0,X2),sK3(X0))
            | ~ r2_hidden(X2,sK3(X0)) )
        & k1_xboole_0 != sK3(X0)
        & r1_tarski(sK3(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1157,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r1_xboole_0(k1_wellord1(X0,X4),X3)
          & r2_hidden(X4,X3) )
     => ( r1_xboole_0(k1_wellord1(X0,sK4(X0,X3)),X3)
        & r2_hidden(sK4(X0,X3),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f1155,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r1_xboole_0(k1_wellord1(X0,X2),X1)
                  | ~ r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r1_xboole_0(k1_wellord1(X0,X4),X3)
                  & r2_hidden(X4,X3) )
              | k1_xboole_0 = X3
              | ~ r1_tarski(X3,k3_relat_1(X0)) )
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1154])).

fof(f1154,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r1_xboole_0(k1_wellord1(X0,X2),X1)
                  | ~ r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                  & r2_hidden(X2,X1) )
              | k1_xboole_0 = X1
              | ~ r1_tarski(X1,k3_relat_1(X0)) )
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1144])).

fof(f1144,plain,(
    ! [X0] :
      ( ( v1_wellord1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                & r2_hidden(X2,X1) )
            | k1_xboole_0 = X1
            | ~ r1_tarski(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1127])).

fof(f1127,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> ! [X1] :
            ~ ( ! [X2] :
                  ~ ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_wellord1)).

fof(f1202,plain,
    ( v1_wellord1(sK0)
    | k1_xboole_0 = sK3(sK0)
    | ~ r1_tarski(sK3(sK0),k3_relat_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f1201])).

fof(f1201,plain,
    ( v1_wellord1(sK0)
    | k1_xboole_0 = sK3(sK0)
    | k1_xboole_0 = sK3(sK0)
    | ~ r1_tarski(sK3(sK0),k3_relat_1(sK0))
    | v1_wellord1(sK0) ),
    inference(resolution,[],[f1198,f1192])).

fof(f1192,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0,X0),X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | v1_wellord1(sK0) ) ),
    inference(resolution,[],[f1188,f1160])).

fof(f1160,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | v1_wellord1(sK0) ),
    inference(cnf_transformation,[],[f1148])).

fof(f1188,plain,(
    ! [X0,X1] :
      ( ~ r1_wellord1(sK0,X1)
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | r2_hidden(sK2(sK0,X0),X0) ) ),
    inference(resolution,[],[f1162,f1159])).

fof(f1162,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = X4
      | ~ r1_tarski(X4,X1)
      | ~ r1_wellord1(X0,X1)
      | r2_hidden(sK2(X0,X4),X4) ) ),
    inference(cnf_transformation,[],[f1153])).

fof(f1153,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_wellord1(X0,X1)
            | ( ! [X3] :
                  ( ~ r1_xboole_0(k1_wellord1(X0,X3),sK1(X0,X1))
                  | ~ r2_hidden(X3,sK1(X0,X1)) )
              & k1_xboole_0 != sK1(X0,X1)
              & r1_tarski(sK1(X0,X1),X1) ) )
          & ( ! [X4] :
                ( ( r1_xboole_0(k1_wellord1(X0,sK2(X0,X4)),X4)
                  & r2_hidden(sK2(X0,X4),X4) )
                | k1_xboole_0 = X4
                | ~ r1_tarski(X4,X1) )
            | ~ r1_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f1150,f1152,f1151])).

fof(f1151,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_xboole_0(k1_wellord1(X0,X3),X2)
              | ~ r2_hidden(X3,X2) )
          & k1_xboole_0 != X2
          & r1_tarski(X2,X1) )
     => ( ! [X3] :
            ( ~ r1_xboole_0(k1_wellord1(X0,X3),sK1(X0,X1))
            | ~ r2_hidden(X3,sK1(X0,X1)) )
        & k1_xboole_0 != sK1(X0,X1)
        & r1_tarski(sK1(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f1152,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( r1_xboole_0(k1_wellord1(X0,X5),X4)
          & r2_hidden(X5,X4) )
     => ( r1_xboole_0(k1_wellord1(X0,sK2(X0,X4)),X4)
        & r2_hidden(sK2(X0,X4),X4) ) ) ),
    introduced(choice_axiom,[])).

fof(f1150,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_wellord1(X0,X1)
            | ? [X2] :
                ( ! [X3] :
                    ( ~ r1_xboole_0(k1_wellord1(X0,X3),X2)
                    | ~ r2_hidden(X3,X2) )
                & k1_xboole_0 != X2
                & r1_tarski(X2,X1) ) )
          & ( ! [X4] :
                ( ? [X5] :
                    ( r1_xboole_0(k1_wellord1(X0,X5),X4)
                    & r2_hidden(X5,X4) )
                | k1_xboole_0 = X4
                | ~ r1_tarski(X4,X1) )
            | ~ r1_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1149])).

fof(f1149,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_wellord1(X0,X1)
            | ? [X2] :
                ( ! [X3] :
                    ( ~ r1_xboole_0(k1_wellord1(X0,X3),X2)
                    | ~ r2_hidden(X3,X2) )
                & k1_xboole_0 != X2
                & r1_tarski(X2,X1) ) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( r1_xboole_0(k1_wellord1(X0,X3),X2)
                    & r2_hidden(X3,X2) )
                | k1_xboole_0 = X2
                | ~ r1_tarski(X2,X1) )
            | ~ r1_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1135])).

fof(f1135,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_wellord1(X0,X1)
        <=> ! [X2] :
              ( ? [X3] :
                  ( r1_xboole_0(k1_wellord1(X0,X3),X2)
                  & r2_hidden(X3,X2) )
              | k1_xboole_0 = X2
              | ~ r1_tarski(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1128])).

fof(f1128,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_wellord1(X0,X1)
        <=> ! [X2] :
              ~ ( ! [X3] :
                    ~ ( r1_xboole_0(k1_wellord1(X0,X3),X2)
                      & r2_hidden(X3,X2) )
                & k1_xboole_0 != X2
                & r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_wellord1)).

fof(f1198,plain,
    ( ~ r2_hidden(sK2(sK0,sK3(sK0)),sK3(sK0))
    | v1_wellord1(sK0)
    | k1_xboole_0 = sK3(sK0) ),
    inference(subsumption_resolution,[],[f1197,f1183])).

fof(f1197,plain,
    ( k1_xboole_0 = sK3(sK0)
    | ~ r1_tarski(sK3(sK0),k3_relat_1(sK0))
    | v1_wellord1(sK0)
    | ~ r2_hidden(sK2(sK0,sK3(sK0)),sK3(sK0)) ),
    inference(subsumption_resolution,[],[f1196,f1159])).

fof(f1196,plain,
    ( k1_xboole_0 = sK3(sK0)
    | ~ r1_tarski(sK3(sK0),k3_relat_1(sK0))
    | v1_wellord1(sK0)
    | ~ r2_hidden(sK2(sK0,sK3(sK0)),sK3(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f1194])).

fof(f1194,plain,
    ( k1_xboole_0 = sK3(sK0)
    | ~ r1_tarski(sK3(sK0),k3_relat_1(sK0))
    | v1_wellord1(sK0)
    | v1_wellord1(sK0)
    | ~ r2_hidden(sK2(sK0,sK3(sK0)),sK3(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f1193,f1181])).

fof(f1181,plain,(
    ! [X2,X0] :
      ( ~ r1_xboole_0(k1_wellord1(X0,X2),sK3(X0))
      | v1_wellord1(X0)
      | ~ r2_hidden(X2,sK3(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1158])).

fof(f1193,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_wellord1(sK0,sK2(sK0,X0)),X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | v1_wellord1(sK0) ) ),
    inference(resolution,[],[f1190,f1160])).

fof(f1190,plain,(
    ! [X0,X1] :
      ( ~ r1_wellord1(sK0,X1)
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | r1_xboole_0(k1_wellord1(sK0,sK2(sK0,X0)),X0) ) ),
    inference(resolution,[],[f1163,f1159])).

fof(f1163,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = X4
      | ~ r1_tarski(X4,X1)
      | ~ r1_wellord1(X0,X1)
      | r1_xboole_0(k1_wellord1(X0,sK2(X0,X4)),X4) ) ),
    inference(cnf_transformation,[],[f1153])).

fof(f1229,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | k1_xboole_0 = sK3(sK0) ),
    inference(subsumption_resolution,[],[f1226,f1159])).

fof(f1226,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | k1_xboole_0 = sK3(sK0) ),
    inference(trivial_inequality_removal,[],[f1224])).

fof(f1224,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | k1_xboole_0 = sK3(sK0) ),
    inference(superposition,[],[f1165,f1220])).

fof(f1220,plain,
    ( k1_xboole_0 = sK1(sK0,k3_relat_1(sK0))
    | k1_xboole_0 = sK3(sK0) ),
    inference(subsumption_resolution,[],[f1219,f1206])).

fof(f1219,plain,
    ( k1_xboole_0 = sK1(sK0,k3_relat_1(sK0))
    | k1_xboole_0 = sK3(sK0)
    | r1_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f1218,f1159])).

fof(f1218,plain,
    ( k1_xboole_0 = sK1(sK0,k3_relat_1(sK0))
    | k1_xboole_0 = sK3(sK0)
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f1217])).

fof(f1217,plain,
    ( k1_xboole_0 = sK1(sK0,k3_relat_1(sK0))
    | k1_xboole_0 = sK3(sK0)
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f1216,f1164])).

fof(f1164,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK1(X0,X1),X1)
      | r1_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1153])).

fof(f1216,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(sK0,X0),k3_relat_1(sK0))
      | k1_xboole_0 = sK1(sK0,X0)
      | k1_xboole_0 = sK3(sK0)
      | r1_wellord1(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f1215,f1210])).

fof(f1210,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,X1),X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(sK0))
      | k1_xboole_0 = sK3(sK0) ) ),
    inference(subsumption_resolution,[],[f1208,f1159])).

fof(f1208,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK3(sK0)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(sK0))
      | r2_hidden(sK4(sK0,X1),X1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f1203,f1177])).

fof(f1177,plain,(
    ! [X0,X3] :
      ( ~ v1_wellord1(X0)
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k3_relat_1(X0))
      | r2_hidden(sK4(X0,X3),X3)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1158])).

fof(f1215,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1(sK0,X0)
      | ~ r1_tarski(sK1(sK0,X0),k3_relat_1(sK0))
      | k1_xboole_0 = sK3(sK0)
      | r1_wellord1(sK0,X0)
      | ~ r2_hidden(sK4(sK0,sK1(sK0,X0)),sK1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f1213,f1159])).

fof(f1213,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1(sK0,X0)
      | ~ r1_tarski(sK1(sK0,X0),k3_relat_1(sK0))
      | k1_xboole_0 = sK3(sK0)
      | r1_wellord1(sK0,X0)
      | ~ r2_hidden(sK4(sK0,sK1(sK0,X0)),sK1(sK0,X0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f1209,f1166])).

fof(f1166,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_xboole_0(k1_wellord1(X0,X3),sK1(X0,X1))
      | r1_wellord1(X0,X1)
      | ~ r2_hidden(X3,sK1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1153])).

fof(f1209,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_wellord1(sK0,sK4(sK0,X0)),X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | k1_xboole_0 = sK3(sK0) ) ),
    inference(subsumption_resolution,[],[f1207,f1159])).

fof(f1207,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3(sK0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | r1_xboole_0(k1_wellord1(sK0,sK4(sK0,X0)),X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f1203,f1178])).

fof(f1178,plain,(
    ! [X0,X3] :
      ( ~ v1_wellord1(X0)
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k3_relat_1(X0))
      | r1_xboole_0(k1_wellord1(X0,sK4(X0,X3)),X3)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1158])).

fof(f1165,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK1(X0,X1)
      | r1_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1153])).

fof(f1180,plain,(
    ! [X0] :
      ( k1_xboole_0 != sK3(X0)
      | v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1158])).

fof(f1161,plain,
    ( ~ v1_wellord1(sK0)
    | ~ r1_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f1148])).

fof(f1263,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f1261])).

fof(f1261,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f1165,f1255])).

fof(f1255,plain,(
    k1_xboole_0 = sK1(sK0,k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f1254,f1159])).

fof(f1254,plain,
    ( k1_xboole_0 = sK1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1253,f1237])).

fof(f1253,plain,
    ( k1_xboole_0 = sK1(sK0,k3_relat_1(sK0))
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f1252,f1164])).

fof(f1252,plain,
    ( ~ r1_tarski(sK1(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))
    | k1_xboole_0 = sK1(sK0,k3_relat_1(sK0)) ),
    inference(resolution,[],[f1251,f1242])).

fof(f1242,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,X1),X1)
      | ~ r1_tarski(X1,k3_relat_1(sK0))
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f1240,f1159])).

fof(f1240,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(sK0))
      | r2_hidden(sK4(sK0,X1),X1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f1236,f1177])).

fof(f1251,plain,(
    ~ r2_hidden(sK4(sK0,sK1(sK0,k3_relat_1(sK0))),sK1(sK0,k3_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f1250,f1159])).

fof(f1250,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK4(sK0,sK1(sK0,k3_relat_1(sK0))),sK1(sK0,k3_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f1249,f1237])).

fof(f1249,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK4(sK0,sK1(sK0,k3_relat_1(sK0))),sK1(sK0,k3_relat_1(sK0))) ),
    inference(duplicate_literal_removal,[],[f1248])).

fof(f1248,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ r2_hidden(sK4(sK0,sK1(sK0,k3_relat_1(sK0))),sK1(sK0,k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f1247,f1166])).

fof(f1247,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_wellord1(sK0,sK4(sK0,sK1(X0,k3_relat_1(sK0)))),sK1(X0,k3_relat_1(sK0)))
      | r1_wellord1(X0,k3_relat_1(sK0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f1245,f1165])).

fof(f1245,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1(X0,k3_relat_1(sK0))
      | r1_xboole_0(k1_wellord1(sK0,sK4(sK0,sK1(X0,k3_relat_1(sK0)))),sK1(X0,k3_relat_1(sK0)))
      | r1_wellord1(X0,k3_relat_1(sK0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f1241,f1164])).

fof(f1241,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_relat_1(sK0))
      | k1_xboole_0 = X0
      | r1_xboole_0(k1_wellord1(sK0,sK4(sK0,X0)),X0) ) ),
    inference(subsumption_resolution,[],[f1239,f1159])).

fof(f1239,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | r1_xboole_0(k1_wellord1(sK0,sK4(sK0,X0)),X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f1236,f1178])).
%------------------------------------------------------------------------------

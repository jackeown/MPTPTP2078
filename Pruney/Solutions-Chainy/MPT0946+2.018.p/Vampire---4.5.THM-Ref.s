%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  217 ( 664 expanded)
%              Number of leaves         :   34 ( 196 expanded)
%              Depth                    :   18
%              Number of atoms          :  764 (3114 expanded)
%              Number of equality atoms :  118 ( 702 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1622,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f162,f195,f236,f380,f390,f427,f583,f1122,f1134,f1135,f1145,f1156,f1270,f1286,f1324,f1340,f1341,f1541,f1595,f1621])).

fof(f1621,plain,
    ( ~ spl5_61
    | ~ spl5_62 ),
    inference(avatar_contradiction_clause,[],[f1620])).

fof(f1620,plain,
    ( $false
    | ~ spl5_61
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f1317,f1152])).

fof(f1152,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f1151])).

% (27678)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f1151,plain,
    ( spl5_62
  <=> r2_hidden(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f1317,plain,
    ( ~ r2_hidden(sK0,sK0)
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f1301,f75])).

fof(f75,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f1301,plain,
    ( ~ r2_hidden(sK0,sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_61 ),
    inference(superposition,[],[f89,f1149])).

fof(f1149,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK0),sK0)
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f1147])).

fof(f1147,plain,
    ( spl5_61
  <=> sK0 = k1_wellord1(k1_wellord2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f89,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0)
                | sK4(X0,X1,X2) = X1
                | ~ r2_hidden(sK4(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0)
                  & sK4(X0,X1,X2) != X1 )
                | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0)
          | sK4(X0,X1,X2) = X1
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0)
            & sK4(X0,X1,X2) != X1 )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f1595,plain,
    ( ~ spl5_1
    | ~ spl5_9
    | spl5_18
    | ~ spl5_40 ),
    inference(avatar_contradiction_clause,[],[f1594])).

fof(f1594,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_9
    | spl5_18
    | ~ spl5_40 ),
    inference(subsumption_resolution,[],[f1593,f119])).

fof(f119,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_1
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1593,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl5_9
    | spl5_18
    | ~ spl5_40 ),
    inference(forward_demodulation,[],[f1590,f619])).

fof(f619,plain,
    ( sK0 = k3_relat_1(k1_wellord2(sK0))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f617])).

fof(f617,plain,
    ( spl5_40
  <=> sK0 = k3_relat_1(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f1590,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))
    | ~ spl5_9
    | spl5_18 ),
    inference(superposition,[],[f433,f1362])).

fof(f1362,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl5_9 ),
    inference(resolution,[],[f1348,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f1348,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_9 ),
    inference(resolution,[],[f207,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f207,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl5_9
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f433,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(k1_wellord2(sK1),X0)))
    | spl5_18 ),
    inference(subsumption_resolution,[],[f428,f75])).

fof(f428,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(k1_wellord2(sK1),X0)))
        | ~ v1_relat_1(k1_wellord2(sK1)) )
    | spl5_18 ),
    inference(resolution,[],[f317,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

fof(f317,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK1)))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl5_18
  <=> r2_hidden(sK1,k3_relat_1(k1_wellord2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f1541,plain,
    ( spl5_38
    | spl5_40
    | ~ spl5_25
    | spl5_39 ),
    inference(avatar_split_clause,[],[f1540,f613,f504,f617,f609])).

fof(f609,plain,
    ( spl5_38
  <=> r2_hidden(k3_relat_1(k1_wellord2(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f504,plain,
    ( spl5_25
  <=> v3_ordinal1(k3_relat_1(k1_wellord2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f613,plain,
    ( spl5_39
  <=> r2_hidden(sK0,k3_relat_1(k1_wellord2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f1540,plain,
    ( sK0 = k3_relat_1(k1_wellord2(sK0))
    | r2_hidden(k3_relat_1(k1_wellord2(sK0)),sK0)
    | ~ spl5_25
    | spl5_39 ),
    inference(subsumption_resolution,[],[f1539,f505])).

fof(f505,plain,
    ( v3_ordinal1(k3_relat_1(k1_wellord2(sK0)))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f504])).

fof(f1539,plain,
    ( sK0 = k3_relat_1(k1_wellord2(sK0))
    | r2_hidden(k3_relat_1(k1_wellord2(sK0)),sK0)
    | ~ v3_ordinal1(k3_relat_1(k1_wellord2(sK0)))
    | spl5_39 ),
    inference(subsumption_resolution,[],[f1533,f49])).

fof(f49,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( sK0 != sK1
    & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
        & v3_ordinal1(X1) )
   => ( sK0 != sK1
      & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

% (27678)Refutation not found, incomplete strategy% (27678)------------------------------
% (27678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27678)Termination reason: Refutation not found, incomplete strategy

% (27678)Memory used [KB]: 1663
% (27678)Time elapsed: 0.097 s
% (27678)------------------------------
% (27678)------------------------------
fof(f1533,plain,
    ( sK0 = k3_relat_1(k1_wellord2(sK0))
    | r2_hidden(k3_relat_1(k1_wellord2(sK0)),sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k3_relat_1(k1_wellord2(sK0)))
    | spl5_39 ),
    inference(resolution,[],[f614,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f614,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK0)))
    | spl5_39 ),
    inference(avatar_component_clause,[],[f613])).

fof(f1341,plain,
    ( spl5_9
    | spl5_8 ),
    inference(avatar_split_clause,[],[f1123,f201,f205])).

fof(f201,plain,
    ( spl5_8
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1123,plain,
    ( r2_xboole_0(sK1,sK0)
    | r2_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f392,f52])).

fof(f52,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f38])).

fof(f392,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK1,sK0)
    | r2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f99,f49])).

fof(f99,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(X2)
      | sK1 = X2
      | r2_xboole_0(sK1,X2)
      | r2_xboole_0(X2,sK1) ) ),
    inference(resolution,[],[f50,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X1,X0)
      | X0 = X1
      | r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_xboole_0(X1,X0)
          | X0 = X1
          | r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_xboole_0(X1,X0)
          | X0 = X1
          | r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).

fof(f50,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f1340,plain,
    ( ~ spl5_38
    | spl5_62 ),
    inference(avatar_contradiction_clause,[],[f1339])).

fof(f1339,plain,
    ( $false
    | ~ spl5_38
    | spl5_62 ),
    inference(subsumption_resolution,[],[f1333,f1153])).

fof(f1153,plain,
    ( ~ r2_hidden(sK0,sK0)
    | spl5_62 ),
    inference(avatar_component_clause,[],[f1151])).

fof(f1333,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f1027,f75])).

fof(f1027,plain,
    ( r2_hidden(sK0,sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_38 ),
    inference(superposition,[],[f611,f85])).

fof(f85,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & r2_hidden(sK3(X0,X1),X0)
            & r2_hidden(sK2(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f611,plain,
    ( r2_hidden(k3_relat_1(k1_wellord2(sK0)),sK0)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f609])).

fof(f1324,plain,
    ( ~ spl5_39
    | ~ spl5_61 ),
    inference(avatar_contradiction_clause,[],[f1323])).

fof(f1323,plain,
    ( $false
    | ~ spl5_39
    | ~ spl5_61 ),
    inference(subsumption_resolution,[],[f1290,f1317])).

fof(f1290,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl5_39 ),
    inference(subsumption_resolution,[],[f1010,f75])).

fof(f1010,plain,
    ( r2_hidden(sK0,sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_39 ),
    inference(superposition,[],[f615,f85])).

fof(f615,plain,
    ( r2_hidden(sK0,k3_relat_1(k1_wellord2(sK0)))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f613])).

fof(f1286,plain,
    ( ~ spl5_39
    | spl5_62 ),
    inference(avatar_contradiction_clause,[],[f1285])).

fof(f1285,plain,
    ( $false
    | ~ spl5_39
    | spl5_62 ),
    inference(subsumption_resolution,[],[f1284,f75])).

fof(f1284,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_39
    | spl5_62 ),
    inference(subsumption_resolution,[],[f1010,f1153])).

fof(f1270,plain,
    ( ~ spl5_1
    | ~ spl5_8
    | ~ spl5_15
    | ~ spl5_40 ),
    inference(avatar_contradiction_clause,[],[f1269])).

fof(f1269,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_8
    | ~ spl5_15
    | ~ spl5_40 ),
    inference(subsumption_resolution,[],[f1268,f209])).

fof(f209,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f203,f53])).

fof(f203,plain,
    ( r2_xboole_0(sK1,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f201])).

fof(f1268,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_40 ),
    inference(subsumption_resolution,[],[f1257,f51])).

fof(f51,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f1257,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ r1_tarski(sK1,sK0)
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_40 ),
    inference(superposition,[],[f1205,f55])).

fof(f1205,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ spl5_1
    | ~ spl5_15
    | ~ spl5_40 ),
    inference(subsumption_resolution,[],[f1204,f119])).

fof(f1204,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ spl5_15
    | ~ spl5_40 ),
    inference(forward_demodulation,[],[f1203,f619])).

fof(f1203,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f1202,f75])).

fof(f1202,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f1192,f96])).

fof(f96,plain,(
    v2_wellord1(k1_wellord2(sK0)) ),
    inference(resolution,[],[f49,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(f1192,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))
    | ~ v2_wellord1(k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_15 ),
    inference(superposition,[],[f73,f292])).

fof(f292,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl5_15
  <=> sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(f1156,plain,
    ( spl5_61
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f263,f1151,f1147])).

fof(f263,plain,
    ( ~ r2_hidden(sK0,sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK0),sK0) ),
    inference(resolution,[],[f94,f49])).

fof(f94,plain,(
    ! [X4] :
      ( ~ v3_ordinal1(X4)
      | ~ r2_hidden(sK0,X4)
      | sK0 = k1_wellord1(k1_wellord2(X4),sK0) ) ),
    inference(resolution,[],[f49,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(f1145,plain,
    ( spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1144,f117,f121])).

fof(f121,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1144,plain,
    ( r2_hidden(sK1,sK0)
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f307,f52])).

fof(f307,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK0)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f97,f49])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | sK1 = X0
      | r2_hidden(sK1,X0)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f50,f63])).

fof(f1135,plain,
    ( spl5_15
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f459,f117,f290])).

fof(f459,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f101,f49])).

fof(f101,plain,(
    ! [X4] :
      ( ~ v3_ordinal1(X4)
      | ~ r2_hidden(sK1,X4)
      | sK1 = k1_wellord1(k1_wellord2(X4),sK1) ) ),
    inference(resolution,[],[f50,f65])).

fof(f1134,plain,
    ( spl5_4
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f1133])).

fof(f1133,plain,
    ( $false
    | spl5_4
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f207,f303])).

fof(f303,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | spl5_4 ),
    inference(resolution,[],[f285,f53])).

fof(f285,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f274,f110])).

fof(f110,plain,(
    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f109,f75])).

fof(f109,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f108,f75])).

fof(f108,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(resolution,[],[f51,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f274,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r1_tarski(sK0,sK1)
    | spl5_4 ),
    inference(superposition,[],[f161,f55])).

fof(f161,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl5_4
  <=> r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1122,plain,
    ( ~ spl5_2
    | ~ spl5_8
    | ~ spl5_19
    | ~ spl5_40 ),
    inference(avatar_contradiction_clause,[],[f1121])).

fof(f1121,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_19
    | ~ spl5_40 ),
    inference(subsumption_resolution,[],[f1116,f165])).

fof(f165,plain,
    ( ~ r2_hidden(sK0,sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f145,f75])).

fof(f145,plain,
    ( ~ r2_hidden(sK0,sK0)
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl5_2 ),
    inference(superposition,[],[f89,f131])).

fof(f131,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f130,f49])).

fof(f130,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ v3_ordinal1(sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f125,f50])).

fof(f125,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f123,f65])).

fof(f123,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f1116,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_19
    | ~ spl5_40 ),
    inference(resolution,[],[f1109,f123])).

fof(f1109,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl5_8
    | ~ spl5_19
    | ~ spl5_40 ),
    inference(forward_demodulation,[],[f464,f619])).

fof(f464,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,k3_relat_1(k1_wellord2(sK0))) )
    | ~ spl5_8
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f463,f322])).

fof(f322,plain,
    ( sK1 = k3_relat_1(k1_wellord2(sK1))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl5_19
  <=> sK1 = k3_relat_1(k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f463,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(k1_wellord2(sK1)))
        | r2_hidden(X0,k3_relat_1(k1_wellord2(sK0))) )
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f461,f75])).

fof(f461,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(k1_wellord2(sK1)))
        | r2_hidden(X0,k3_relat_1(k1_wellord2(sK0)))
        | ~ v1_relat_1(k1_wellord2(sK0)) )
    | ~ spl5_8 ),
    inference(superposition,[],[f76,f211])).

fof(f211,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl5_8 ),
    inference(resolution,[],[f209,f55])).

fof(f583,plain,(
    spl5_25 ),
    inference(avatar_contradiction_clause,[],[f582])).

fof(f582,plain,
    ( $false
    | spl5_25 ),
    inference(subsumption_resolution,[],[f581,f75])).

fof(f581,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | spl5_25 ),
    inference(subsumption_resolution,[],[f580,f49])).

fof(f580,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl5_25 ),
    inference(superposition,[],[f506,f85])).

fof(f506,plain,
    ( ~ v3_ordinal1(k3_relat_1(k1_wellord2(sK0)))
    | spl5_25 ),
    inference(avatar_component_clause,[],[f504])).

fof(f427,plain,
    ( spl5_17
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | spl5_17
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f425,f75])).

fof(f425,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | spl5_17
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f416,f391])).

fof(f391,plain,
    ( ~ r2_hidden(sK1,sK1)
    | spl5_17 ),
    inference(subsumption_resolution,[],[f384,f75])).

fof(f384,plain,
    ( ~ r2_hidden(sK1,sK1)
    | ~ v1_relat_1(k1_wellord2(sK1))
    | spl5_17 ),
    inference(superposition,[],[f313,f85])).

fof(f313,plain,
    ( ~ r2_hidden(k3_relat_1(k1_wellord2(sK1)),sK1)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl5_17
  <=> r2_hidden(k3_relat_1(k1_wellord2(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f416,plain,
    ( r2_hidden(sK1,sK1)
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl5_18 ),
    inference(superposition,[],[f318,f85])).

fof(f318,plain,
    ( r2_hidden(sK1,k3_relat_1(k1_wellord2(sK1)))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f316])).

fof(f390,plain,
    ( spl5_18
    | spl5_19
    | ~ spl5_5
    | spl5_17 ),
    inference(avatar_split_clause,[],[f389,f312,f179,f320,f316])).

fof(f179,plain,
    ( spl5_5
  <=> v3_ordinal1(k3_relat_1(k1_wellord2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f389,plain,
    ( sK1 = k3_relat_1(k1_wellord2(sK1))
    | r2_hidden(sK1,k3_relat_1(k1_wellord2(sK1)))
    | ~ spl5_5
    | spl5_17 ),
    inference(subsumption_resolution,[],[f388,f50])).

fof(f388,plain,
    ( sK1 = k3_relat_1(k1_wellord2(sK1))
    | r2_hidden(sK1,k3_relat_1(k1_wellord2(sK1)))
    | ~ v3_ordinal1(sK1)
    | ~ spl5_5
    | spl5_17 ),
    inference(subsumption_resolution,[],[f383,f180])).

fof(f180,plain,
    ( v3_ordinal1(k3_relat_1(k1_wellord2(sK1)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f179])).

fof(f383,plain,
    ( sK1 = k3_relat_1(k1_wellord2(sK1))
    | r2_hidden(sK1,k3_relat_1(k1_wellord2(sK1)))
    | ~ v3_ordinal1(k3_relat_1(k1_wellord2(sK1)))
    | ~ v3_ordinal1(sK1)
    | spl5_17 ),
    inference(resolution,[],[f313,f63])).

fof(f380,plain,(
    ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f378,f75])).

fof(f378,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f362,f341])).

fof(f341,plain,
    ( r2_hidden(sK1,sK1)
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f334,f75])).

fof(f334,plain,
    ( r2_hidden(sK1,sK1)
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl5_17 ),
    inference(superposition,[],[f314,f85])).

fof(f314,plain,
    ( r2_hidden(k3_relat_1(k1_wellord2(sK1)),sK1)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f312])).

fof(f362,plain,
    ( ~ r2_hidden(sK1,sK1)
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl5_17 ),
    inference(superposition,[],[f89,f348])).

fof(f348,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK1),sK1)
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f347,f50])).

fof(f347,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK1),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ spl5_17 ),
    inference(duplicate_literal_removal,[],[f342])).

fof(f342,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK1),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK1)
    | ~ spl5_17 ),
    inference(resolution,[],[f341,f65])).

fof(f236,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl5_5 ),
    inference(subsumption_resolution,[],[f234,f75])).

fof(f234,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | spl5_5 ),
    inference(subsumption_resolution,[],[f233,f50])).

fof(f233,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v1_relat_1(k1_wellord2(sK1))
    | spl5_5 ),
    inference(superposition,[],[f181,f85])).

fof(f181,plain,
    ( ~ v3_ordinal1(k3_relat_1(k1_wellord2(sK1)))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f179])).

fof(f195,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f193,f75])).

fof(f193,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f175,f123])).

fof(f175,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v1_relat_1(k1_wellord2(sK1))
    | spl5_3 ),
    inference(superposition,[],[f157,f85])).

fof(f157,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl5_3
  <=> r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f162,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f153,f121,f159,f155])).

fof(f153,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f152,f75])).

fof(f152,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f142,f103])).

fof(f103,plain,(
    v2_wellord1(k1_wellord2(sK1)) ),
    inference(resolution,[],[f50,f74])).

fof(f142,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ v2_wellord1(k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl5_2 ),
    inference(superposition,[],[f73,f131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (27682)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.46  % (27673)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.46  % (27666)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (27666)Refutation not found, incomplete strategy% (27666)------------------------------
% 0.20/0.46  % (27666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (27666)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (27666)Memory used [KB]: 10618
% 0.20/0.46  % (27666)Time elapsed: 0.051 s
% 0.20/0.46  % (27666)------------------------------
% 0.20/0.46  % (27666)------------------------------
% 0.20/0.47  % (27684)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.47  % (27665)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (27679)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (27665)Refutation not found, incomplete strategy% (27665)------------------------------
% 0.20/0.48  % (27665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (27665)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (27665)Memory used [KB]: 6268
% 0.20/0.48  % (27665)Time elapsed: 0.056 s
% 0.20/0.48  % (27665)------------------------------
% 0.20/0.48  % (27665)------------------------------
% 0.20/0.48  % (27672)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (27669)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (27667)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (27668)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (27670)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (27674)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (27681)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  % (27684)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f1622,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f162,f195,f236,f380,f390,f427,f583,f1122,f1134,f1135,f1145,f1156,f1270,f1286,f1324,f1340,f1341,f1541,f1595,f1621])).
% 0.20/0.50  fof(f1621,plain,(
% 0.20/0.50    ~spl5_61 | ~spl5_62),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f1620])).
% 0.20/0.50  fof(f1620,plain,(
% 0.20/0.50    $false | (~spl5_61 | ~spl5_62)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1317,f1152])).
% 0.20/0.50  fof(f1152,plain,(
% 0.20/0.50    r2_hidden(sK0,sK0) | ~spl5_62),
% 0.20/0.50    inference(avatar_component_clause,[],[f1151])).
% 0.20/0.50  % (27678)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  fof(f1151,plain,(
% 0.20/0.50    spl5_62 <=> r2_hidden(sK0,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 0.20/0.50  fof(f1317,plain,(
% 0.20/0.50    ~r2_hidden(sK0,sK0) | ~spl5_61),
% 0.20/0.50    inference(subsumption_resolution,[],[f1301,f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.20/0.50  fof(f1301,plain,(
% 0.20/0.50    ~r2_hidden(sK0,sK0) | ~v1_relat_1(k1_wellord2(sK0)) | ~spl5_61),
% 0.20/0.50    inference(superposition,[],[f89,f1149])).
% 0.20/0.50  fof(f1149,plain,(
% 0.20/0.50    sK0 = k1_wellord1(k1_wellord2(sK0),sK0) | ~spl5_61),
% 0.20/0.50    inference(avatar_component_clause,[],[f1147])).
% 0.20/0.50  fof(f1147,plain,(
% 0.20/0.50    spl5_61 <=> sK0 = k1_wellord1(k1_wellord2(sK0),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f88])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0) | sK4(X0,X1,X2) = X1 | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0) & sK4(X0,X1,X2) != X1) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0) | sK4(X0,X1,X2) = X1 | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0) & sK4(X0,X1,X2) != X1) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(rectify,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 0.20/0.50  fof(f1595,plain,(
% 0.20/0.50    ~spl5_1 | ~spl5_9 | spl5_18 | ~spl5_40),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f1594])).
% 0.20/0.50  fof(f1594,plain,(
% 0.20/0.50    $false | (~spl5_1 | ~spl5_9 | spl5_18 | ~spl5_40)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1593,f119])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    r2_hidden(sK1,sK0) | ~spl5_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f117])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    spl5_1 <=> r2_hidden(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.50  fof(f1593,plain,(
% 0.20/0.50    ~r2_hidden(sK1,sK0) | (~spl5_9 | spl5_18 | ~spl5_40)),
% 0.20/0.50    inference(forward_demodulation,[],[f1590,f619])).
% 0.20/0.50  fof(f619,plain,(
% 0.20/0.50    sK0 = k3_relat_1(k1_wellord2(sK0)) | ~spl5_40),
% 0.20/0.50    inference(avatar_component_clause,[],[f617])).
% 0.20/0.50  fof(f617,plain,(
% 0.20/0.50    spl5_40 <=> sK0 = k3_relat_1(k1_wellord2(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.20/0.50  fof(f1590,plain,(
% 0.20/0.50    ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) | (~spl5_9 | spl5_18)),
% 0.20/0.50    inference(superposition,[],[f433,f1362])).
% 0.20/0.50  fof(f1362,plain,(
% 0.20/0.50    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | ~spl5_9),
% 0.20/0.50    inference(resolution,[],[f1348,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 0.20/0.50  fof(f1348,plain,(
% 0.20/0.50    r1_tarski(sK0,sK1) | ~spl5_9),
% 0.20/0.50    inference(resolution,[],[f207,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1] : (r2_xboole_0(X0,X1) => (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.50    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    r2_xboole_0(sK0,sK1) | ~spl5_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f205])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    spl5_9 <=> r2_xboole_0(sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.50  fof(f433,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK1,k3_relat_1(k2_wellord1(k1_wellord2(sK1),X0)))) ) | spl5_18),
% 0.20/0.50    inference(subsumption_resolution,[],[f428,f75])).
% 0.20/0.50  fof(f428,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK1,k3_relat_1(k2_wellord1(k1_wellord2(sK1),X0))) | ~v1_relat_1(k1_wellord2(sK1))) ) | spl5_18),
% 0.20/0.50    inference(resolution,[],[f317,f76])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).
% 0.20/0.50  fof(f317,plain,(
% 0.20/0.50    ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK1))) | spl5_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f316])).
% 0.20/0.50  fof(f316,plain,(
% 0.20/0.50    spl5_18 <=> r2_hidden(sK1,k3_relat_1(k1_wellord2(sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.50  fof(f1541,plain,(
% 0.20/0.50    spl5_38 | spl5_40 | ~spl5_25 | spl5_39),
% 0.20/0.50    inference(avatar_split_clause,[],[f1540,f613,f504,f617,f609])).
% 0.20/0.50  fof(f609,plain,(
% 0.20/0.50    spl5_38 <=> r2_hidden(k3_relat_1(k1_wellord2(sK0)),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.20/0.50  fof(f504,plain,(
% 0.20/0.50    spl5_25 <=> v3_ordinal1(k3_relat_1(k1_wellord2(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.20/0.50  fof(f613,plain,(
% 0.20/0.50    spl5_39 <=> r2_hidden(sK0,k3_relat_1(k1_wellord2(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.20/0.50  fof(f1540,plain,(
% 0.20/0.50    sK0 = k3_relat_1(k1_wellord2(sK0)) | r2_hidden(k3_relat_1(k1_wellord2(sK0)),sK0) | (~spl5_25 | spl5_39)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1539,f505])).
% 0.20/0.50  fof(f505,plain,(
% 0.20/0.50    v3_ordinal1(k3_relat_1(k1_wellord2(sK0))) | ~spl5_25),
% 0.20/0.50    inference(avatar_component_clause,[],[f504])).
% 0.20/0.50  fof(f1539,plain,(
% 0.20/0.50    sK0 = k3_relat_1(k1_wellord2(sK0)) | r2_hidden(k3_relat_1(k1_wellord2(sK0)),sK0) | ~v3_ordinal1(k3_relat_1(k1_wellord2(sK0))) | spl5_39),
% 0.20/0.50    inference(subsumption_resolution,[],[f1533,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    v3_ordinal1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f37,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.20/0.50    inference(negated_conjecture,[],[f13])).
% 0.20/0.50  fof(f13,conjecture,(
% 0.20/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).
% 0.20/0.50  % (27678)Refutation not found, incomplete strategy% (27678)------------------------------
% 0.20/0.50  % (27678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27678)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (27678)Memory used [KB]: 1663
% 0.20/0.50  % (27678)Time elapsed: 0.097 s
% 0.20/0.50  % (27678)------------------------------
% 0.20/0.50  % (27678)------------------------------
% 0.20/0.50  fof(f1533,plain,(
% 0.20/0.50    sK0 = k3_relat_1(k1_wellord2(sK0)) | r2_hidden(k3_relat_1(k1_wellord2(sK0)),sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(k3_relat_1(k1_wellord2(sK0))) | spl5_39),
% 0.20/0.50    inference(resolution,[],[f614,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.50    inference(flattening,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.20/0.50  fof(f614,plain,(
% 0.20/0.50    ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK0))) | spl5_39),
% 0.20/0.50    inference(avatar_component_clause,[],[f613])).
% 0.20/0.50  fof(f1341,plain,(
% 0.20/0.50    spl5_9 | spl5_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f1123,f201,f205])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    spl5_8 <=> r2_xboole_0(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.50  fof(f1123,plain,(
% 0.20/0.50    r2_xboole_0(sK1,sK0) | r2_xboole_0(sK0,sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f392,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    sK0 != sK1),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f392,plain,(
% 0.20/0.50    sK0 = sK1 | r2_xboole_0(sK1,sK0) | r2_xboole_0(sK0,sK1)),
% 0.20/0.50    inference(resolution,[],[f99,f49])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ( ! [X2] : (~v3_ordinal1(X2) | sK1 = X2 | r2_xboole_0(sK1,X2) | r2_xboole_0(X2,sK1)) )),
% 0.20/0.50    inference(resolution,[],[f50,f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.50    inference(flattening,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    v3_ordinal1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f1340,plain,(
% 0.20/0.50    ~spl5_38 | spl5_62),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f1339])).
% 0.20/0.50  fof(f1339,plain,(
% 0.20/0.50    $false | (~spl5_38 | spl5_62)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1333,f1153])).
% 0.20/0.50  fof(f1153,plain,(
% 0.20/0.50    ~r2_hidden(sK0,sK0) | spl5_62),
% 0.20/0.50    inference(avatar_component_clause,[],[f1151])).
% 0.20/0.50  fof(f1333,plain,(
% 0.20/0.50    r2_hidden(sK0,sK0) | ~spl5_38),
% 0.20/0.50    inference(subsumption_resolution,[],[f1027,f75])).
% 0.20/0.50  fof(f1027,plain,(
% 0.20/0.50    r2_hidden(sK0,sK0) | ~v1_relat_1(k1_wellord2(sK0)) | ~spl5_38),
% 0.20/0.50    inference(superposition,[],[f611,f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.50    inference(equality_resolution,[],[f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(rectify,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.20/0.50  fof(f611,plain,(
% 0.20/0.50    r2_hidden(k3_relat_1(k1_wellord2(sK0)),sK0) | ~spl5_38),
% 0.20/0.50    inference(avatar_component_clause,[],[f609])).
% 0.20/0.50  fof(f1324,plain,(
% 0.20/0.50    ~spl5_39 | ~spl5_61),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f1323])).
% 0.20/0.50  fof(f1323,plain,(
% 0.20/0.50    $false | (~spl5_39 | ~spl5_61)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1290,f1317])).
% 0.20/0.50  fof(f1290,plain,(
% 0.20/0.50    r2_hidden(sK0,sK0) | ~spl5_39),
% 0.20/0.50    inference(subsumption_resolution,[],[f1010,f75])).
% 0.20/0.50  fof(f1010,plain,(
% 0.20/0.50    r2_hidden(sK0,sK0) | ~v1_relat_1(k1_wellord2(sK0)) | ~spl5_39),
% 0.20/0.50    inference(superposition,[],[f615,f85])).
% 0.20/0.50  fof(f615,plain,(
% 0.20/0.50    r2_hidden(sK0,k3_relat_1(k1_wellord2(sK0))) | ~spl5_39),
% 0.20/0.50    inference(avatar_component_clause,[],[f613])).
% 0.20/0.50  fof(f1286,plain,(
% 0.20/0.50    ~spl5_39 | spl5_62),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f1285])).
% 0.20/0.50  fof(f1285,plain,(
% 0.20/0.50    $false | (~spl5_39 | spl5_62)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1284,f75])).
% 0.20/0.50  fof(f1284,plain,(
% 0.20/0.50    ~v1_relat_1(k1_wellord2(sK0)) | (~spl5_39 | spl5_62)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1010,f1153])).
% 0.20/0.50  fof(f1270,plain,(
% 0.20/0.50    ~spl5_1 | ~spl5_8 | ~spl5_15 | ~spl5_40),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f1269])).
% 0.20/0.50  fof(f1269,plain,(
% 0.20/0.50    $false | (~spl5_1 | ~spl5_8 | ~spl5_15 | ~spl5_40)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1268,f209])).
% 0.20/0.50  fof(f209,plain,(
% 0.20/0.50    r1_tarski(sK1,sK0) | ~spl5_8),
% 0.20/0.50    inference(resolution,[],[f203,f53])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    r2_xboole_0(sK1,sK0) | ~spl5_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f201])).
% 0.20/0.50  fof(f1268,plain,(
% 0.20/0.50    ~r1_tarski(sK1,sK0) | (~spl5_1 | ~spl5_15 | ~spl5_40)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1257,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f1257,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~r1_tarski(sK1,sK0) | (~spl5_1 | ~spl5_15 | ~spl5_40)),
% 0.20/0.50    inference(superposition,[],[f1205,f55])).
% 0.20/0.50  fof(f1205,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | (~spl5_1 | ~spl5_15 | ~spl5_40)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1204,f119])).
% 0.20/0.50  fof(f1204,plain,(
% 0.20/0.50    ~r2_hidden(sK1,sK0) | ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | (~spl5_15 | ~spl5_40)),
% 0.20/0.50    inference(forward_demodulation,[],[f1203,f619])).
% 0.20/0.50  fof(f1203,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) | ~spl5_15),
% 0.20/0.50    inference(subsumption_resolution,[],[f1202,f75])).
% 0.20/0.50  fof(f1202,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) | ~v1_relat_1(k1_wellord2(sK0)) | ~spl5_15),
% 0.20/0.50    inference(subsumption_resolution,[],[f1192,f96])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    v2_wellord1(k1_wellord2(sK0))),
% 0.20/0.50    inference(resolution,[],[f49,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).
% 0.20/0.50  fof(f1192,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) | ~v2_wellord1(k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK0)) | ~spl5_15),
% 0.20/0.50    inference(superposition,[],[f73,f292])).
% 0.20/0.50  fof(f292,plain,(
% 0.20/0.50    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~spl5_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f290])).
% 0.20/0.50  fof(f290,plain,(
% 0.20/0.50    spl5_15 <=> sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).
% 0.20/0.50  fof(f1156,plain,(
% 0.20/0.50    spl5_61 | ~spl5_62),
% 0.20/0.50    inference(avatar_split_clause,[],[f263,f1151,f1147])).
% 0.20/0.50  fof(f263,plain,(
% 0.20/0.50    ~r2_hidden(sK0,sK0) | sK0 = k1_wellord1(k1_wellord2(sK0),sK0)),
% 0.20/0.50    inference(resolution,[],[f94,f49])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ( ! [X4] : (~v3_ordinal1(X4) | ~r2_hidden(sK0,X4) | sK0 = k1_wellord1(k1_wellord2(X4),sK0)) )),
% 0.20/0.50    inference(resolution,[],[f49,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.50    inference(flattening,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).
% 0.20/0.50  fof(f1145,plain,(
% 0.20/0.50    spl5_2 | spl5_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f1144,f117,f121])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    spl5_2 <=> r2_hidden(sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.50  fof(f1144,plain,(
% 0.20/0.50    r2_hidden(sK1,sK0) | r2_hidden(sK0,sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f307,f52])).
% 0.20/0.50  fof(f307,plain,(
% 0.20/0.50    sK0 = sK1 | r2_hidden(sK1,sK0) | r2_hidden(sK0,sK1)),
% 0.20/0.50    inference(resolution,[],[f97,f49])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    ( ! [X0] : (~v3_ordinal1(X0) | sK1 = X0 | r2_hidden(sK1,X0) | r2_hidden(X0,sK1)) )),
% 0.20/0.50    inference(resolution,[],[f50,f63])).
% 0.20/0.50  fof(f1135,plain,(
% 0.20/0.50    spl5_15 | ~spl5_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f459,f117,f290])).
% 0.20/0.50  fof(f459,plain,(
% 0.20/0.50    ~r2_hidden(sK1,sK0) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.20/0.50    inference(resolution,[],[f101,f49])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    ( ! [X4] : (~v3_ordinal1(X4) | ~r2_hidden(sK1,X4) | sK1 = k1_wellord1(k1_wellord2(X4),sK1)) )),
% 0.20/0.50    inference(resolution,[],[f50,f65])).
% 0.20/0.50  fof(f1134,plain,(
% 0.20/0.50    spl5_4 | ~spl5_9),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f1133])).
% 0.20/0.50  fof(f1133,plain,(
% 0.20/0.50    $false | (spl5_4 | ~spl5_9)),
% 0.20/0.50    inference(subsumption_resolution,[],[f207,f303])).
% 0.20/0.50  fof(f303,plain,(
% 0.20/0.50    ~r2_xboole_0(sK0,sK1) | spl5_4),
% 0.20/0.50    inference(resolution,[],[f285,f53])).
% 0.20/0.50  fof(f285,plain,(
% 0.20/0.50    ~r1_tarski(sK0,sK1) | spl5_4),
% 0.20/0.50    inference(subsumption_resolution,[],[f274,f110])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f109,f75])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f108,f75])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK0))),
% 0.20/0.50    inference(resolution,[],[f51,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 0.20/0.50  fof(f274,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~r1_tarski(sK0,sK1) | spl5_4),
% 0.20/0.50    inference(superposition,[],[f161,f55])).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | spl5_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f159])).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    spl5_4 <=> r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.50  fof(f1122,plain,(
% 0.20/0.50    ~spl5_2 | ~spl5_8 | ~spl5_19 | ~spl5_40),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f1121])).
% 0.20/0.50  fof(f1121,plain,(
% 0.20/0.50    $false | (~spl5_2 | ~spl5_8 | ~spl5_19 | ~spl5_40)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1116,f165])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    ~r2_hidden(sK0,sK0) | ~spl5_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f145,f75])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    ~r2_hidden(sK0,sK0) | ~v1_relat_1(k1_wellord2(sK1)) | ~spl5_2),
% 0.20/0.50    inference(superposition,[],[f89,f131])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~spl5_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f130,f49])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~v3_ordinal1(sK0) | ~spl5_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f125,f50])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~spl5_2),
% 0.20/0.50    inference(resolution,[],[f123,f65])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    r2_hidden(sK0,sK1) | ~spl5_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f121])).
% 0.20/0.50  fof(f1116,plain,(
% 0.20/0.50    r2_hidden(sK0,sK0) | (~spl5_2 | ~spl5_8 | ~spl5_19 | ~spl5_40)),
% 0.20/0.50    inference(resolution,[],[f1109,f123])).
% 0.20/0.50  fof(f1109,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) ) | (~spl5_8 | ~spl5_19 | ~spl5_40)),
% 0.20/0.50    inference(forward_demodulation,[],[f464,f619])).
% 0.20/0.50  fof(f464,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,k3_relat_1(k1_wellord2(sK0)))) ) | (~spl5_8 | ~spl5_19)),
% 0.20/0.50    inference(forward_demodulation,[],[f463,f322])).
% 0.20/0.50  fof(f322,plain,(
% 0.20/0.50    sK1 = k3_relat_1(k1_wellord2(sK1)) | ~spl5_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f320])).
% 0.20/0.50  fof(f320,plain,(
% 0.20/0.50    spl5_19 <=> sK1 = k3_relat_1(k1_wellord2(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.50  fof(f463,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(k1_wellord2(sK1))) | r2_hidden(X0,k3_relat_1(k1_wellord2(sK0)))) ) | ~spl5_8),
% 0.20/0.50    inference(subsumption_resolution,[],[f461,f75])).
% 0.20/0.50  fof(f461,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(k1_wellord2(sK1))) | r2_hidden(X0,k3_relat_1(k1_wellord2(sK0))) | ~v1_relat_1(k1_wellord2(sK0))) ) | ~spl5_8),
% 0.20/0.50    inference(superposition,[],[f76,f211])).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | ~spl5_8),
% 0.20/0.50    inference(resolution,[],[f209,f55])).
% 0.20/0.50  fof(f583,plain,(
% 0.20/0.50    spl5_25),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f582])).
% 0.20/0.50  fof(f582,plain,(
% 0.20/0.50    $false | spl5_25),
% 0.20/0.50    inference(subsumption_resolution,[],[f581,f75])).
% 0.20/0.50  fof(f581,plain,(
% 0.20/0.50    ~v1_relat_1(k1_wellord2(sK0)) | spl5_25),
% 0.20/0.50    inference(subsumption_resolution,[],[f580,f49])).
% 0.20/0.50  fof(f580,plain,(
% 0.20/0.50    ~v3_ordinal1(sK0) | ~v1_relat_1(k1_wellord2(sK0)) | spl5_25),
% 0.20/0.50    inference(superposition,[],[f506,f85])).
% 0.20/0.50  fof(f506,plain,(
% 0.20/0.50    ~v3_ordinal1(k3_relat_1(k1_wellord2(sK0))) | spl5_25),
% 0.20/0.50    inference(avatar_component_clause,[],[f504])).
% 0.20/0.50  fof(f427,plain,(
% 0.20/0.50    spl5_17 | ~spl5_18),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f426])).
% 0.20/0.50  fof(f426,plain,(
% 0.20/0.50    $false | (spl5_17 | ~spl5_18)),
% 0.20/0.50    inference(subsumption_resolution,[],[f425,f75])).
% 0.20/0.50  fof(f425,plain,(
% 0.20/0.50    ~v1_relat_1(k1_wellord2(sK1)) | (spl5_17 | ~spl5_18)),
% 0.20/0.50    inference(subsumption_resolution,[],[f416,f391])).
% 0.20/0.50  fof(f391,plain,(
% 0.20/0.50    ~r2_hidden(sK1,sK1) | spl5_17),
% 0.20/0.50    inference(subsumption_resolution,[],[f384,f75])).
% 0.20/0.50  fof(f384,plain,(
% 0.20/0.50    ~r2_hidden(sK1,sK1) | ~v1_relat_1(k1_wellord2(sK1)) | spl5_17),
% 0.20/0.50    inference(superposition,[],[f313,f85])).
% 0.20/0.50  fof(f313,plain,(
% 0.20/0.50    ~r2_hidden(k3_relat_1(k1_wellord2(sK1)),sK1) | spl5_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f312])).
% 0.20/0.50  fof(f312,plain,(
% 0.20/0.50    spl5_17 <=> r2_hidden(k3_relat_1(k1_wellord2(sK1)),sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.50  fof(f416,plain,(
% 0.20/0.50    r2_hidden(sK1,sK1) | ~v1_relat_1(k1_wellord2(sK1)) | ~spl5_18),
% 0.20/0.50    inference(superposition,[],[f318,f85])).
% 0.20/0.50  fof(f318,plain,(
% 0.20/0.50    r2_hidden(sK1,k3_relat_1(k1_wellord2(sK1))) | ~spl5_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f316])).
% 0.20/0.50  fof(f390,plain,(
% 0.20/0.50    spl5_18 | spl5_19 | ~spl5_5 | spl5_17),
% 0.20/0.50    inference(avatar_split_clause,[],[f389,f312,f179,f320,f316])).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    spl5_5 <=> v3_ordinal1(k3_relat_1(k1_wellord2(sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.50  fof(f389,plain,(
% 0.20/0.50    sK1 = k3_relat_1(k1_wellord2(sK1)) | r2_hidden(sK1,k3_relat_1(k1_wellord2(sK1))) | (~spl5_5 | spl5_17)),
% 0.20/0.50    inference(subsumption_resolution,[],[f388,f50])).
% 0.20/0.50  fof(f388,plain,(
% 0.20/0.50    sK1 = k3_relat_1(k1_wellord2(sK1)) | r2_hidden(sK1,k3_relat_1(k1_wellord2(sK1))) | ~v3_ordinal1(sK1) | (~spl5_5 | spl5_17)),
% 0.20/0.50    inference(subsumption_resolution,[],[f383,f180])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    v3_ordinal1(k3_relat_1(k1_wellord2(sK1))) | ~spl5_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f179])).
% 0.20/0.50  fof(f383,plain,(
% 0.20/0.50    sK1 = k3_relat_1(k1_wellord2(sK1)) | r2_hidden(sK1,k3_relat_1(k1_wellord2(sK1))) | ~v3_ordinal1(k3_relat_1(k1_wellord2(sK1))) | ~v3_ordinal1(sK1) | spl5_17),
% 0.20/0.50    inference(resolution,[],[f313,f63])).
% 0.20/0.50  fof(f380,plain,(
% 0.20/0.50    ~spl5_17),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f379])).
% 0.20/0.50  fof(f379,plain,(
% 0.20/0.50    $false | ~spl5_17),
% 0.20/0.50    inference(subsumption_resolution,[],[f378,f75])).
% 0.20/0.50  fof(f378,plain,(
% 0.20/0.50    ~v1_relat_1(k1_wellord2(sK1)) | ~spl5_17),
% 0.20/0.50    inference(subsumption_resolution,[],[f362,f341])).
% 0.20/0.50  fof(f341,plain,(
% 0.20/0.50    r2_hidden(sK1,sK1) | ~spl5_17),
% 0.20/0.50    inference(subsumption_resolution,[],[f334,f75])).
% 0.20/0.50  fof(f334,plain,(
% 0.20/0.50    r2_hidden(sK1,sK1) | ~v1_relat_1(k1_wellord2(sK1)) | ~spl5_17),
% 0.20/0.50    inference(superposition,[],[f314,f85])).
% 0.20/0.50  fof(f314,plain,(
% 0.20/0.50    r2_hidden(k3_relat_1(k1_wellord2(sK1)),sK1) | ~spl5_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f312])).
% 0.20/0.50  fof(f362,plain,(
% 0.20/0.50    ~r2_hidden(sK1,sK1) | ~v1_relat_1(k1_wellord2(sK1)) | ~spl5_17),
% 0.20/0.50    inference(superposition,[],[f89,f348])).
% 0.20/0.50  fof(f348,plain,(
% 0.20/0.50    sK1 = k1_wellord1(k1_wellord2(sK1),sK1) | ~spl5_17),
% 0.20/0.50    inference(subsumption_resolution,[],[f347,f50])).
% 0.20/0.50  fof(f347,plain,(
% 0.20/0.50    sK1 = k1_wellord1(k1_wellord2(sK1),sK1) | ~v3_ordinal1(sK1) | ~spl5_17),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f342])).
% 0.20/0.50  fof(f342,plain,(
% 0.20/0.50    sK1 = k1_wellord1(k1_wellord2(sK1),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK1) | ~spl5_17),
% 0.20/0.50    inference(resolution,[],[f341,f65])).
% 0.20/0.50  fof(f236,plain,(
% 0.20/0.50    spl5_5),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f235])).
% 0.20/0.50  fof(f235,plain,(
% 0.20/0.50    $false | spl5_5),
% 0.20/0.50    inference(subsumption_resolution,[],[f234,f75])).
% 0.20/0.50  fof(f234,plain,(
% 0.20/0.50    ~v1_relat_1(k1_wellord2(sK1)) | spl5_5),
% 0.20/0.50    inference(subsumption_resolution,[],[f233,f50])).
% 0.20/0.50  fof(f233,plain,(
% 0.20/0.50    ~v3_ordinal1(sK1) | ~v1_relat_1(k1_wellord2(sK1)) | spl5_5),
% 0.20/0.50    inference(superposition,[],[f181,f85])).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    ~v3_ordinal1(k3_relat_1(k1_wellord2(sK1))) | spl5_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f179])).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    ~spl5_2 | spl5_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f194])).
% 0.20/0.50  fof(f194,plain,(
% 0.20/0.50    $false | (~spl5_2 | spl5_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f193,f75])).
% 0.20/0.50  fof(f193,plain,(
% 0.20/0.50    ~v1_relat_1(k1_wellord2(sK1)) | (~spl5_2 | spl5_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f175,f123])).
% 0.20/0.50  fof(f175,plain,(
% 0.20/0.50    ~r2_hidden(sK0,sK1) | ~v1_relat_1(k1_wellord2(sK1)) | spl5_3),
% 0.20/0.50    inference(superposition,[],[f157,f85])).
% 0.20/0.50  fof(f157,plain,(
% 0.20/0.50    ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | spl5_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f155])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    spl5_3 <=> r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    ~spl5_3 | ~spl5_4 | ~spl5_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f153,f121,f159,f155])).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | ~spl5_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f152,f75])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | ~v1_relat_1(k1_wellord2(sK1)) | ~spl5_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f142,f103])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    v2_wellord1(k1_wellord2(sK1))),
% 0.20/0.50    inference(resolution,[],[f50,f74])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | ~v2_wellord1(k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK1)) | ~spl5_2),
% 0.20/0.50    inference(superposition,[],[f73,f131])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (27684)------------------------------
% 0.20/0.50  % (27684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27684)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (27684)Memory used [KB]: 6652
% 0.20/0.50  % (27684)Time elapsed: 0.087 s
% 0.20/0.50  % (27684)------------------------------
% 0.20/0.50  % (27684)------------------------------
% 0.20/0.50  % (27671)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (27680)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (27668)Refutation not found, incomplete strategy% (27668)------------------------------
% 0.20/0.50  % (27668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27668)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (27668)Memory used [KB]: 10874
% 0.20/0.50  % (27664)Success in time 0.147 s
%------------------------------------------------------------------------------

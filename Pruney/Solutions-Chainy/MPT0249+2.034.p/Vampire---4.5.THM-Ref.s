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
% DateTime   : Thu Dec  3 12:38:15 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 429 expanded)
%              Number of leaves         :   47 ( 162 expanded)
%              Depth                    :   12
%              Number of atoms          :  441 (1158 expanded)
%              Number of equality atoms :  119 ( 386 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5154,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f104,f111,f151,f174,f180,f235,f266,f272,f503,f507,f542,f545,f582,f809,f989,f1001,f1238,f1306,f1456,f1575,f2129,f4898,f5018,f5105,f5151,f5152])).

fof(f5152,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f5151,plain,
    ( spl4_37
    | ~ spl4_56 ),
    inference(avatar_contradiction_clause,[],[f5149])).

fof(f5149,plain,
    ( $false
    | spl4_37
    | ~ spl4_56 ),
    inference(subsumption_resolution,[],[f1237,f5121])).

fof(f5121,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_56 ),
    inference(superposition,[],[f186,f5104])).

fof(f5104,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f5102])).

fof(f5102,plain,
    ( spl4_56
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f186,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f181,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f181,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(resolution,[],[f56,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f1237,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl4_37 ),
    inference(avatar_component_clause,[],[f1235])).

fof(f1235,plain,
    ( spl4_37
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f5105,plain,
    ( spl4_56
    | ~ spl4_39
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f5044,f5015,f1453,f5102])).

fof(f1453,plain,
    ( spl4_39
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f5015,plain,
    ( spl4_55
  <=> sK2 = k2_xboole_0(sK2,k2_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f5044,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)
    | ~ spl4_55 ),
    inference(superposition,[],[f290,f5017])).

fof(f5017,plain,
    ( sK2 = k2_xboole_0(sK2,k2_xboole_0(sK1,sK1))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f5015])).

fof(f290,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X3,k2_xboole_0(X4,X5)),X4)
      | k1_xboole_0 = k2_xboole_0(k1_xboole_0,X4) ) ),
    inference(forward_demodulation,[],[f289,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f289,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,X4)
      | ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X3,X4),X5),X4) ) ),
    inference(forward_demodulation,[],[f288,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f288,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X3,k2_xboole_0(X4,X5))),X4)
      | ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X3,X4),X5),X4) ) ),
    inference(forward_demodulation,[],[f279,f44])).

fof(f279,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X3,X4),X5)),X4)
      | ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X3,X4),X5),X4) ) ),
    inference(superposition,[],[f57,f41])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f5018,plain,
    ( spl4_55
    | ~ spl4_45
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f4934,f4895,f2126,f5015])).

fof(f2126,plain,
    ( spl4_45
  <=> sK2 = k2_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f4895,plain,
    ( spl4_52
  <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f4934,plain,
    ( sK2 = k2_xboole_0(sK2,k2_xboole_0(sK1,sK1))
    | ~ spl4_45
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f4909,f2128])).

fof(f2128,plain,
    ( sK2 = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f2126])).

fof(f4909,plain,
    ( k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK1))
    | ~ spl4_52 ),
    inference(superposition,[],[f46,f4897])).

fof(f4897,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK1,sK1),sK2)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f4895])).

fof(f4898,plain,
    ( spl4_52
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f4815,f1303,f4895])).

fof(f1303,plain,
    ( spl4_38
  <=> sK2 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f4815,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK1,sK1),sK2)
    | ~ spl4_38 ),
    inference(superposition,[],[f1322,f1305])).

fof(f1305,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f1303])).

fof(f1322,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X3,sK1),k2_xboole_0(X3,sK2))
    | ~ spl4_38 ),
    inference(superposition,[],[f218,f1305])).

fof(f218,plain,(
    ! [X6,X8,X7] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,k2_xboole_0(X7,X8))) ),
    inference(superposition,[],[f41,f44])).

fof(f2129,plain,
    ( ~ spl4_29
    | spl4_45
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f1606,f1572,f2126,f579])).

fof(f579,plain,
    ( spl4_29
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f1572,plain,
    ( spl4_40
  <=> k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f1606,plain,
    ( sK2 = k2_xboole_0(sK2,k1_xboole_0)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl4_40 ),
    inference(superposition,[],[f1574,f449])).

fof(f449,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0) ) ),
    inference(global_subsumption,[],[f72,f448])).

fof(f448,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f444])).

fof(f444,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0)
      | k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f55,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,sK3(X0,X1,X2))
      | k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK3(X0,X1,X2))
        & r1_tarski(X2,sK3(X0,X1,X2))
        & r1_tarski(X0,sK3(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK3(X0,X1,X2))
        & r1_tarski(X2,sK3(X0,X1,X2))
        & r1_tarski(X0,sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,sK3(X0,X1,X2))
      | k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1574,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f1572])).

fof(f1575,plain,
    ( spl4_40
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f1156,f806,f1572])).

fof(f806,plain,
    ( spl4_33
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f1156,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_33 ),
    inference(superposition,[],[f46,f808])).

fof(f808,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f806])).

fof(f1456,plain,
    ( spl4_39
    | spl4_14
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f1450,f263,f177,f1453])).

fof(f177,plain,
    ( spl4_14
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f263,plain,
    ( spl4_19
  <=> sK2 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f1450,plain,
    ( r1_xboole_0(sK2,sK1)
    | spl4_14
    | ~ spl4_19 ),
    inference(resolution,[],[f1142,f179])).

fof(f179,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f177])).

fof(f1142,plain,
    ( ! [X9] :
        ( r2_hidden(sK0,X9)
        | r1_xboole_0(sK2,X9) )
    | ~ spl4_19 ),
    inference(superposition,[],[f51,f265])).

fof(f265,plain,
    ( sK2 = k1_tarski(sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f263])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f1306,plain,
    ( spl4_38
    | ~ spl4_11
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f1127,f263,f148,f1303])).

fof(f148,plain,
    ( spl4_11
  <=> k1_tarski(sK0) = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1127,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl4_11
    | ~ spl4_19 ),
    inference(superposition,[],[f150,f265])).

fof(f150,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f148])).

fof(f1238,plain,
    ( ~ spl4_37
    | spl4_2
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f990,f192,f80,f1235])).

fof(f80,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f192,plain,
    ( spl4_15
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f990,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_15 ),
    inference(resolution,[],[f193,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f193,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f192])).

fof(f1001,plain,
    ( spl4_3
    | ~ spl4_25
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f996])).

fof(f996,plain,
    ( $false
    | spl4_3
    | ~ spl4_25
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f541,f87,f987,f66])).

fof(f987,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_25 ),
    inference(resolution,[],[f690,f72])).

fof(f690,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,X0)
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl4_25 ),
    inference(superposition,[],[f498,f449])).

fof(f498,plain,
    ( ! [X2] : r1_tarski(k1_xboole_0,k2_xboole_0(X2,X2))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f497])).

fof(f497,plain,
    ( spl4_25
  <=> ! [X2] : r1_tarski(k1_xboole_0,k2_xboole_0(X2,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f87,plain,
    ( k1_xboole_0 != sK2
    | spl4_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f541,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f539])).

% (19259)Time limit reached!
% (19259)------------------------------
% (19259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19259)Termination reason: Time limit
% (19259)Termination phase: Saturation

% (19259)Memory used [KB]: 13816
% (19259)Time elapsed: 0.400 s
% (19259)------------------------------
% (19259)------------------------------
fof(f539,plain,
    ( spl4_28
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f989,plain,
    ( spl4_15
    | ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f986])).

fof(f986,plain,
    ( $false
    | spl4_15
    | ~ spl4_25 ),
    inference(unit_resulting_resolution,[],[f194,f72,f690])).

fof(f194,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f192])).

fof(f809,plain,
    ( spl4_33
    | ~ spl4_7
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f655,f263,f108,f806])).

fof(f108,plain,
    ( spl4_7
  <=> k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f655,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl4_7
    | ~ spl4_19 ),
    inference(superposition,[],[f110,f265])).

fof(f110,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f582,plain,
    ( spl4_29
    | ~ spl4_6
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f552,f263,f101,f579])).

fof(f101,plain,
    ( spl4_6
  <=> r1_tarski(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f552,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_6
    | ~ spl4_19 ),
    inference(superposition,[],[f103,f265])).

fof(f103,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f545,plain,
    ( spl4_20
    | spl4_27 ),
    inference(avatar_contradiction_clause,[],[f543])).

fof(f543,plain,
    ( $false
    | spl4_20
    | spl4_27 ),
    inference(unit_resulting_resolution,[],[f271,f537,f51])).

fof(f537,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK2)
    | spl4_27 ),
    inference(avatar_component_clause,[],[f535])).

fof(f535,plain,
    ( spl4_27
  <=> r1_xboole_0(k1_tarski(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f271,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl4_20
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f542,plain,
    ( ~ spl4_27
    | spl4_28
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f533,f90,f539,f535])).

fof(f90,plain,
    ( spl4_4
  <=> k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f533,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ r1_xboole_0(k1_tarski(sK0),sK2)
    | ~ spl4_4 ),
    inference(superposition,[],[f521,f116])).

fof(f116,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f59,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

fof(f521,plain,
    ( ! [X7] :
        ( r1_tarski(sK2,k4_xboole_0(k1_tarski(sK0),X7))
        | ~ r1_xboole_0(X7,sK2) )
    | ~ spl4_4 ),
    inference(superposition,[],[f186,f277])).

fof(f277,plain,
    ( ! [X11] :
        ( k2_xboole_0(k4_xboole_0(sK1,X11),sK2) = k4_xboole_0(k1_tarski(sK0),X11)
        | ~ r1_xboole_0(X11,sK2) )
    | ~ spl4_4 ),
    inference(superposition,[],[f57,f92])).

fof(f92,plain,
    ( k2_xboole_0(sK1,sK2) = k1_tarski(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f507,plain,(
    spl4_26 ),
    inference(avatar_contradiction_clause,[],[f504])).

fof(f504,plain,
    ( $false
    | spl4_26 ),
    inference(unit_resulting_resolution,[],[f72,f502])).

fof(f502,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_26 ),
    inference(avatar_component_clause,[],[f500])).

fof(f500,plain,
    ( spl4_26
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f503,plain,
    ( spl4_25
    | ~ spl4_26
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f487,f90,f500,f497])).

fof(f487,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
        | r1_tarski(k1_xboole_0,k2_xboole_0(X2,X2)) )
    | ~ spl4_4 ),
    inference(superposition,[],[f380,f116])).

fof(f380,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,k4_xboole_0(X1,X0))
        | r1_tarski(k1_xboole_0,k2_xboole_0(X0,X1)) )
    | ~ spl4_4 ),
    inference(superposition,[],[f337,f46])).

fof(f337,plain,
    ( ! [X4,X3] :
        ( r1_tarski(k1_xboole_0,k2_xboole_0(X3,X4))
        | ~ r1_tarski(k1_xboole_0,X4) )
    | ~ spl4_4 ),
    inference(superposition,[],[f56,f327])).

fof(f327,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f326,f302])).

fof(f302,plain,
    ( ! [X6] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),X6))
    | ~ spl4_4 ),
    inference(superposition,[],[f41,f212])).

fof(f212,plain,
    ( ! [X11] : k2_xboole_0(sK1,k2_xboole_0(sK2,X11)) = k2_xboole_0(k1_tarski(sK0),X11)
    | ~ spl4_4 ),
    inference(superposition,[],[f44,f92])).

fof(f326,plain,
    ( ! [X0,X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(X0,X1)))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f321,f44])).

fof(f321,plain,
    ( ! [X0,X1] : k4_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),X0),X1)) = k4_xboole_0(k1_xboole_0,X1)
    | ~ spl4_4 ),
    inference(superposition,[],[f45,f302])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f272,plain,
    ( ~ spl4_20
    | spl4_18 ),
    inference(avatar_split_clause,[],[f267,f259,f269])).

fof(f259,plain,
    ( spl4_18
  <=> r1_tarski(k1_tarski(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f267,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl4_18 ),
    inference(resolution,[],[f261,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f261,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK2)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f259])).

fof(f266,plain,
    ( ~ spl4_18
    | spl4_19
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f236,f232,f263,f259])).

fof(f232,plain,
    ( spl4_17
  <=> r1_tarski(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f236,plain,
    ( sK2 = k1_tarski(sK0)
    | ~ r1_tarski(k1_tarski(sK0),sK2)
    | ~ spl4_17 ),
    inference(resolution,[],[f234,f66])).

fof(f234,plain,
    ( r1_tarski(sK2,k1_tarski(sK0))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f232])).

fof(f235,plain,
    ( spl4_17
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f203,f90,f232])).

fof(f203,plain,
    ( r1_tarski(sK2,k1_tarski(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f186,f92])).

fof(f180,plain,
    ( ~ spl4_14
    | spl4_12 ),
    inference(avatar_split_clause,[],[f175,f167,f177])).

fof(f167,plain,
    ( spl4_12
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f175,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_12 ),
    inference(resolution,[],[f169,f50])).

fof(f169,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f167])).

fof(f174,plain,
    ( ~ spl4_12
    | spl4_13
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f164,f101,f171,f167])).

fof(f171,plain,
    ( spl4_13
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f164,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f66,f103])).

fof(f151,plain,
    ( spl4_11
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f141,f90,f148])).

fof(f141,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f47,f92])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f111,plain,
    ( spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f106,f90,f108])).

fof(f106,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f41,f92])).

fof(f104,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f99,f90,f101])).

fof(f99,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl4_4 ),
    inference(superposition,[],[f58,f92])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f93,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f37,f90])).

fof(f37,plain,(
    k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f88,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f40,f85])).

fof(f40,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f39,f80])).

fof(f39,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f38,f75])).

fof(f75,plain,
    ( spl4_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f38,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (810614784)
% 0.14/0.37  ipcrm: permission denied for id (810680324)
% 0.14/0.37  ipcrm: permission denied for id (810713096)
% 0.14/0.38  ipcrm: permission denied for id (810844173)
% 0.14/0.38  ipcrm: permission denied for id (810876942)
% 0.14/0.38  ipcrm: permission denied for id (810909711)
% 0.22/0.39  ipcrm: permission denied for id (811073559)
% 0.22/0.40  ipcrm: permission denied for id (811139097)
% 0.22/0.40  ipcrm: permission denied for id (811204638)
% 0.22/0.40  ipcrm: permission denied for id (811237407)
% 0.22/0.40  ipcrm: permission denied for id (811270176)
% 0.22/0.41  ipcrm: permission denied for id (811335715)
% 0.22/0.41  ipcrm: permission denied for id (811368484)
% 0.22/0.41  ipcrm: permission denied for id (811401253)
% 0.22/0.41  ipcrm: permission denied for id (811434022)
% 0.22/0.42  ipcrm: permission denied for id (811565101)
% 0.22/0.42  ipcrm: permission denied for id (811630640)
% 0.22/0.43  ipcrm: permission denied for id (811696179)
% 0.22/0.43  ipcrm: permission denied for id (811761717)
% 0.22/0.43  ipcrm: permission denied for id (811827255)
% 0.22/0.44  ipcrm: permission denied for id (811892793)
% 0.22/0.44  ipcrm: permission denied for id (811925563)
% 0.22/0.45  ipcrm: permission denied for id (812122180)
% 0.22/0.45  ipcrm: permission denied for id (812154950)
% 0.22/0.45  ipcrm: permission denied for id (812187719)
% 0.22/0.45  ipcrm: permission denied for id (812220488)
% 0.22/0.46  ipcrm: permission denied for id (812253257)
% 0.22/0.46  ipcrm: permission denied for id (812318795)
% 0.22/0.47  ipcrm: permission denied for id (812384338)
% 0.22/0.47  ipcrm: permission denied for id (812417107)
% 0.22/0.47  ipcrm: permission denied for id (812548183)
% 0.22/0.48  ipcrm: permission denied for id (812613722)
% 0.22/0.48  ipcrm: permission denied for id (812744797)
% 0.22/0.48  ipcrm: permission denied for id (812810336)
% 0.22/0.49  ipcrm: permission denied for id (812843105)
% 0.22/0.49  ipcrm: permission denied for id (812875874)
% 0.22/0.49  ipcrm: permission denied for id (812908643)
% 0.22/0.49  ipcrm: permission denied for id (812941412)
% 0.22/0.49  ipcrm: permission denied for id (812974181)
% 0.22/0.49  ipcrm: permission denied for id (813006950)
% 0.22/0.50  ipcrm: permission denied for id (813105257)
% 0.22/0.50  ipcrm: permission denied for id (813138027)
% 0.22/0.50  ipcrm: permission denied for id (813203565)
% 0.22/0.50  ipcrm: permission denied for id (813269104)
% 0.22/0.51  ipcrm: permission denied for id (813334643)
% 0.22/0.51  ipcrm: permission denied for id (813400182)
% 0.22/0.52  ipcrm: permission denied for id (813629567)
% 0.39/0.66  % (19238)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.39/0.67  % (19252)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.39/0.68  % (19259)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.39/0.68  % (19254)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.39/0.69  % (19247)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.39/0.69  % (19263)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.39/0.69  % (19237)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.39/0.69  % (19262)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.39/0.69  % (19236)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.39/0.69  % (19244)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.39/0.70  % (19255)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.39/0.70  % (19264)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.39/0.70  % (19249)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.39/0.70  % (19250)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.39/0.70  % (19239)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.39/0.70  % (19241)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.39/0.70  % (19264)Refutation not found, incomplete strategy% (19264)------------------------------
% 0.39/0.70  % (19264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.70  % (19256)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.39/0.70  % (19264)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.70  
% 0.39/0.70  % (19264)Memory used [KB]: 1663
% 0.39/0.70  % (19264)Time elapsed: 0.069 s
% 0.39/0.70  % (19264)------------------------------
% 0.39/0.70  % (19264)------------------------------
% 0.39/0.70  % (19251)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.39/0.70  % (19240)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.39/0.70  % (19251)Refutation not found, incomplete strategy% (19251)------------------------------
% 0.39/0.70  % (19251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.70  % (19251)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.70  
% 0.39/0.70  % (19251)Memory used [KB]: 10618
% 0.39/0.70  % (19251)Time elapsed: 0.131 s
% 0.39/0.70  % (19251)------------------------------
% 0.39/0.70  % (19251)------------------------------
% 0.39/0.71  % (19258)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.39/0.71  % (19235)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.39/0.71  % (19242)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.39/0.71  % (19246)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.39/0.71  % (19257)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.39/0.71  % (19260)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.39/0.72  % (19248)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.39/0.72  % (19261)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.39/0.72  % (19253)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.39/0.73  % (19243)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.50/0.73  % (19245)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.50/0.83  % (19238)Refutation not found, incomplete strategy% (19238)------------------------------
% 0.50/0.83  % (19238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.50/0.83  % (19238)Termination reason: Refutation not found, incomplete strategy
% 0.50/0.83  
% 0.50/0.83  % (19238)Memory used [KB]: 6140
% 0.50/0.83  % (19238)Time elapsed: 0.243 s
% 0.50/0.83  % (19238)------------------------------
% 0.50/0.83  % (19238)------------------------------
% 0.50/0.85  % (19265)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 0.58/0.87  % (19266)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 0.58/0.96  % (19258)Refutation found. Thanks to Tanya!
% 0.58/0.96  % SZS status Theorem for theBenchmark
% 0.58/0.96  % SZS output start Proof for theBenchmark
% 0.58/0.96  fof(f5154,plain,(
% 0.58/0.96    $false),
% 0.58/0.96    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f104,f111,f151,f174,f180,f235,f266,f272,f503,f507,f542,f545,f582,f809,f989,f1001,f1238,f1306,f1456,f1575,f2129,f4898,f5018,f5105,f5151,f5152])).
% 0.58/0.96  fof(f5152,plain,(
% 0.58/0.96    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0) | sK1 = sK2),
% 0.58/0.96    introduced(theory_tautology_sat_conflict,[])).
% 0.58/0.96  fof(f5151,plain,(
% 0.58/0.96    spl4_37 | ~spl4_56),
% 0.58/0.96    inference(avatar_contradiction_clause,[],[f5149])).
% 0.58/0.96  fof(f5149,plain,(
% 0.58/0.96    $false | (spl4_37 | ~spl4_56)),
% 0.58/0.96    inference(subsumption_resolution,[],[f1237,f5121])).
% 0.58/0.96  fof(f5121,plain,(
% 0.58/0.96    r1_tarski(sK1,k1_xboole_0) | ~spl4_56),
% 0.58/0.96    inference(superposition,[],[f186,f5104])).
% 0.58/0.96  fof(f5104,plain,(
% 0.58/0.96    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) | ~spl4_56),
% 0.58/0.96    inference(avatar_component_clause,[],[f5102])).
% 0.58/0.96  fof(f5102,plain,(
% 0.58/0.96    spl4_56 <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)),
% 0.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.58/0.96  fof(f186,plain,(
% 0.58/0.96    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.58/0.96    inference(forward_demodulation,[],[f181,f46])).
% 0.58/0.96  fof(f46,plain,(
% 0.58/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.58/0.96    inference(cnf_transformation,[],[f3])).
% 0.58/0.96  fof(f3,axiom,(
% 0.58/0.96    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.58/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.58/0.96  fof(f181,plain,(
% 0.58/0.96    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 0.58/0.96    inference(resolution,[],[f56,f72])).
% 0.58/0.96  fof(f72,plain,(
% 0.58/0.96    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.58/0.96    inference(equality_resolution,[],[f65])).
% 0.58/0.96  fof(f65,plain,(
% 0.58/0.96    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.58/0.96    inference(cnf_transformation,[],[f36])).
% 0.58/0.96  fof(f36,plain,(
% 0.58/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.58/0.96    inference(flattening,[],[f35])).
% 0.58/0.96  fof(f35,plain,(
% 0.58/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.58/0.96    inference(nnf_transformation,[],[f1])).
% 0.58/0.96  fof(f1,axiom,(
% 0.58/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.58/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.58/0.96  fof(f56,plain,(
% 0.58/0.96    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.58/0.96    inference(cnf_transformation,[],[f28])).
% 0.58/0.96  fof(f28,plain,(
% 0.58/0.96    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.58/0.96    inference(ennf_transformation,[],[f5])).
% 0.58/0.96  fof(f5,axiom,(
% 0.58/0.96    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.58/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.58/0.96  fof(f1237,plain,(
% 0.58/0.96    ~r1_tarski(sK1,k1_xboole_0) | spl4_37),
% 0.58/0.96    inference(avatar_component_clause,[],[f1235])).
% 0.58/0.96  fof(f1235,plain,(
% 0.58/0.96    spl4_37 <=> r1_tarski(sK1,k1_xboole_0)),
% 0.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.58/0.96  fof(f5105,plain,(
% 0.58/0.96    spl4_56 | ~spl4_39 | ~spl4_55),
% 0.58/0.96    inference(avatar_split_clause,[],[f5044,f5015,f1453,f5102])).
% 0.58/0.96  fof(f1453,plain,(
% 0.58/0.96    spl4_39 <=> r1_xboole_0(sK2,sK1)),
% 0.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.58/0.96  fof(f5015,plain,(
% 0.58/0.96    spl4_55 <=> sK2 = k2_xboole_0(sK2,k2_xboole_0(sK1,sK1))),
% 0.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 0.58/0.96  fof(f5044,plain,(
% 0.58/0.96    ~r1_xboole_0(sK2,sK1) | k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) | ~spl4_55),
% 0.58/0.96    inference(superposition,[],[f290,f5017])).
% 0.58/0.96  fof(f5017,plain,(
% 0.58/0.96    sK2 = k2_xboole_0(sK2,k2_xboole_0(sK1,sK1)) | ~spl4_55),
% 0.58/0.96    inference(avatar_component_clause,[],[f5015])).
% 0.58/0.96  fof(f290,plain,(
% 0.58/0.96    ( ! [X4,X5,X3] : (~r1_xboole_0(k2_xboole_0(X3,k2_xboole_0(X4,X5)),X4) | k1_xboole_0 = k2_xboole_0(k1_xboole_0,X4)) )),
% 0.58/0.96    inference(forward_demodulation,[],[f289,f44])).
% 0.58/0.96  fof(f44,plain,(
% 0.58/0.96    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.58/0.96    inference(cnf_transformation,[],[f7])).
% 0.58/0.96  fof(f7,axiom,(
% 0.58/0.96    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.58/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.58/0.96  fof(f289,plain,(
% 0.58/0.96    ( ! [X4,X5,X3] : (k1_xboole_0 = k2_xboole_0(k1_xboole_0,X4) | ~r1_xboole_0(k2_xboole_0(k2_xboole_0(X3,X4),X5),X4)) )),
% 0.58/0.96    inference(forward_demodulation,[],[f288,f41])).
% 0.58/0.96  fof(f41,plain,(
% 0.58/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.58/0.96    inference(cnf_transformation,[],[f6])).
% 0.58/0.96  fof(f6,axiom,(
% 0.58/0.96    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.58/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.58/0.96  fof(f288,plain,(
% 0.58/0.96    ( ! [X4,X5,X3] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X3,k2_xboole_0(X4,X5))),X4) | ~r1_xboole_0(k2_xboole_0(k2_xboole_0(X3,X4),X5),X4)) )),
% 0.58/0.96    inference(forward_demodulation,[],[f279,f44])).
% 0.58/0.96  fof(f279,plain,(
% 0.58/0.96    ( ! [X4,X5,X3] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X3,X4),X5)),X4) | ~r1_xboole_0(k2_xboole_0(k2_xboole_0(X3,X4),X5),X4)) )),
% 0.58/0.96    inference(superposition,[],[f57,f41])).
% 0.58/0.96  fof(f57,plain,(
% 0.58/0.96    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1)) )),
% 0.58/0.96    inference(cnf_transformation,[],[f29])).
% 0.58/0.96  fof(f29,plain,(
% 0.58/0.96    ! [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1))),
% 0.58/0.96    inference(ennf_transformation,[],[f12])).
% 0.58/0.96  fof(f12,axiom,(
% 0.58/0.96    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 0.58/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).
% 0.58/0.96  fof(f5018,plain,(
% 0.58/0.96    spl4_55 | ~spl4_45 | ~spl4_52),
% 0.58/0.96    inference(avatar_split_clause,[],[f4934,f4895,f2126,f5015])).
% 0.58/0.96  fof(f2126,plain,(
% 0.58/0.96    spl4_45 <=> sK2 = k2_xboole_0(sK2,k1_xboole_0)),
% 0.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.58/0.96  fof(f4895,plain,(
% 0.58/0.96    spl4_52 <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK1,sK1),sK2)),
% 0.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 0.58/0.96  fof(f4934,plain,(
% 0.58/0.96    sK2 = k2_xboole_0(sK2,k2_xboole_0(sK1,sK1)) | (~spl4_45 | ~spl4_52)),
% 0.58/0.96    inference(forward_demodulation,[],[f4909,f2128])).
% 0.58/0.96  fof(f2128,plain,(
% 0.58/0.96    sK2 = k2_xboole_0(sK2,k1_xboole_0) | ~spl4_45),
% 0.58/0.96    inference(avatar_component_clause,[],[f2126])).
% 0.58/0.96  fof(f4909,plain,(
% 0.58/0.96    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK1)) | ~spl4_52),
% 0.58/0.96    inference(superposition,[],[f46,f4897])).
% 0.58/0.96  fof(f4897,plain,(
% 0.58/0.96    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK1,sK1),sK2) | ~spl4_52),
% 0.58/0.96    inference(avatar_component_clause,[],[f4895])).
% 0.58/0.96  fof(f4898,plain,(
% 0.58/0.96    spl4_52 | ~spl4_38),
% 0.58/0.96    inference(avatar_split_clause,[],[f4815,f1303,f4895])).
% 0.58/0.96  fof(f1303,plain,(
% 0.58/0.96    spl4_38 <=> sK2 = k2_xboole_0(sK1,sK2)),
% 0.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.58/0.96  fof(f4815,plain,(
% 0.58/0.96    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK1,sK1),sK2) | ~spl4_38),
% 0.58/0.96    inference(superposition,[],[f1322,f1305])).
% 0.58/0.96  fof(f1305,plain,(
% 0.58/0.96    sK2 = k2_xboole_0(sK1,sK2) | ~spl4_38),
% 0.58/0.96    inference(avatar_component_clause,[],[f1303])).
% 0.58/0.96  fof(f1322,plain,(
% 0.58/0.96    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X3,sK1),k2_xboole_0(X3,sK2))) ) | ~spl4_38),
% 0.58/0.96    inference(superposition,[],[f218,f1305])).
% 0.58/0.96  fof(f218,plain,(
% 0.58/0.96    ( ! [X6,X8,X7] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,k2_xboole_0(X7,X8)))) )),
% 0.58/0.96    inference(superposition,[],[f41,f44])).
% 0.58/0.96  fof(f2129,plain,(
% 0.58/0.96    ~spl4_29 | spl4_45 | ~spl4_40),
% 0.58/0.96    inference(avatar_split_clause,[],[f1606,f1572,f2126,f579])).
% 0.58/0.96  fof(f579,plain,(
% 0.58/0.96    spl4_29 <=> r1_tarski(sK1,sK2)),
% 0.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.58/0.96  fof(f1572,plain,(
% 0.58/0.96    spl4_40 <=> k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0)),
% 0.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.58/0.96  fof(f1606,plain,(
% 0.58/0.96    sK2 = k2_xboole_0(sK2,k1_xboole_0) | ~r1_tarski(sK1,sK2) | ~spl4_40),
% 0.58/0.96    inference(superposition,[],[f1574,f449])).
% 0.58/0.96  fof(f449,plain,(
% 0.58/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0)) )),
% 0.58/0.96    inference(global_subsumption,[],[f72,f448])).
% 0.58/0.96  fof(f448,plain,(
% 0.58/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 0.58/0.96    inference(duplicate_literal_removal,[],[f444])).
% 0.58/0.96  fof(f444,plain,(
% 0.58/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0) | k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 0.58/0.96    inference(resolution,[],[f55,f53])).
% 0.58/0.96  fof(f53,plain,(
% 0.58/0.96    ( ! [X2,X0,X1] : (r1_tarski(X0,sK3(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.58/0.96    inference(cnf_transformation,[],[f34])).
% 0.58/0.96  fof(f34,plain,(
% 0.58/0.96    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK3(X0,X1,X2)) & r1_tarski(X2,sK3(X0,X1,X2)) & r1_tarski(X0,sK3(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.58/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f33])).
% 0.58/0.96  fof(f33,plain,(
% 0.58/0.96    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK3(X0,X1,X2)) & r1_tarski(X2,sK3(X0,X1,X2)) & r1_tarski(X0,sK3(X0,X1,X2))))),
% 0.58/0.96    introduced(choice_axiom,[])).
% 0.58/0.96  fof(f27,plain,(
% 0.58/0.96    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.58/0.96    inference(flattening,[],[f26])).
% 0.58/0.96  fof(f26,plain,(
% 0.58/0.96    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.58/0.96    inference(ennf_transformation,[],[f2])).
% 0.58/0.96  fof(f2,axiom,(
% 0.58/0.96    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 0.58/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).
% 0.58/0.96  fof(f55,plain,(
% 0.58/0.96    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK3(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.58/0.96    inference(cnf_transformation,[],[f34])).
% 0.58/0.96  fof(f1574,plain,(
% 0.58/0.96    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) | ~spl4_40),
% 0.58/0.96    inference(avatar_component_clause,[],[f1572])).
% 0.58/0.96  fof(f1575,plain,(
% 0.58/0.96    spl4_40 | ~spl4_33),
% 0.58/0.96    inference(avatar_split_clause,[],[f1156,f806,f1572])).
% 0.58/0.96  fof(f806,plain,(
% 0.58/0.96    spl4_33 <=> k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.58/0.96  fof(f1156,plain,(
% 0.58/0.96    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) | ~spl4_33),
% 0.58/0.96    inference(superposition,[],[f46,f808])).
% 0.58/0.96  fof(f808,plain,(
% 0.58/0.96    k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~spl4_33),
% 0.58/0.96    inference(avatar_component_clause,[],[f806])).
% 0.58/0.96  fof(f1456,plain,(
% 0.58/0.96    spl4_39 | spl4_14 | ~spl4_19),
% 0.58/0.96    inference(avatar_split_clause,[],[f1450,f263,f177,f1453])).
% 0.58/0.96  fof(f177,plain,(
% 0.58/0.96    spl4_14 <=> r2_hidden(sK0,sK1)),
% 0.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.58/0.96  fof(f263,plain,(
% 0.58/0.96    spl4_19 <=> sK2 = k1_tarski(sK0)),
% 0.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.58/0.96  fof(f1450,plain,(
% 0.58/0.96    r1_xboole_0(sK2,sK1) | (spl4_14 | ~spl4_19)),
% 0.58/0.96    inference(resolution,[],[f1142,f179])).
% 0.58/0.96  fof(f179,plain,(
% 0.58/0.96    ~r2_hidden(sK0,sK1) | spl4_14),
% 0.58/0.96    inference(avatar_component_clause,[],[f177])).
% 0.58/0.96  fof(f1142,plain,(
% 0.58/0.96    ( ! [X9] : (r2_hidden(sK0,X9) | r1_xboole_0(sK2,X9)) ) | ~spl4_19),
% 0.58/0.96    inference(superposition,[],[f51,f265])).
% 0.58/0.96  fof(f265,plain,(
% 0.58/0.96    sK2 = k1_tarski(sK0) | ~spl4_19),
% 0.58/0.96    inference(avatar_component_clause,[],[f263])).
% 0.58/0.96  fof(f51,plain,(
% 0.58/0.96    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.58/0.96    inference(cnf_transformation,[],[f25])).
% 0.58/0.96  fof(f25,plain,(
% 0.58/0.96    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.58/0.96    inference(ennf_transformation,[],[f19])).
% 0.58/0.96  fof(f19,axiom,(
% 0.58/0.96    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.58/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.58/0.96  fof(f1306,plain,(
% 0.58/0.96    spl4_38 | ~spl4_11 | ~spl4_19),
% 0.58/0.96    inference(avatar_split_clause,[],[f1127,f263,f148,f1303])).
% 0.58/0.96  fof(f148,plain,(
% 0.58/0.96    spl4_11 <=> k1_tarski(sK0) = k2_xboole_0(sK1,k1_tarski(sK0))),
% 0.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.58/0.96  fof(f1127,plain,(
% 0.58/0.96    sK2 = k2_xboole_0(sK1,sK2) | (~spl4_11 | ~spl4_19)),
% 0.58/0.96    inference(superposition,[],[f150,f265])).
% 0.58/0.96  fof(f150,plain,(
% 0.58/0.96    k1_tarski(sK0) = k2_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_11),
% 0.58/0.96    inference(avatar_component_clause,[],[f148])).
% 0.58/0.96  fof(f1238,plain,(
% 0.58/0.96    ~spl4_37 | spl4_2 | ~spl4_15),
% 0.58/0.96    inference(avatar_split_clause,[],[f990,f192,f80,f1235])).
% 0.58/0.96  fof(f80,plain,(
% 0.58/0.96    spl4_2 <=> k1_xboole_0 = sK1),
% 0.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.58/0.96  fof(f192,plain,(
% 0.58/0.96    spl4_15 <=> r1_tarski(k1_xboole_0,sK1)),
% 0.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.58/0.96  fof(f990,plain,(
% 0.58/0.96    k1_xboole_0 = sK1 | ~r1_tarski(sK1,k1_xboole_0) | ~spl4_15),
% 0.58/0.96    inference(resolution,[],[f193,f66])).
% 0.58/0.96  fof(f66,plain,(
% 0.58/0.96    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.58/0.96    inference(cnf_transformation,[],[f36])).
% 0.58/0.96  fof(f193,plain,(
% 0.58/0.96    r1_tarski(k1_xboole_0,sK1) | ~spl4_15),
% 0.58/0.96    inference(avatar_component_clause,[],[f192])).
% 0.58/0.96  fof(f1001,plain,(
% 0.58/0.96    spl4_3 | ~spl4_25 | ~spl4_28),
% 0.58/0.96    inference(avatar_contradiction_clause,[],[f996])).
% 0.58/0.96  fof(f996,plain,(
% 0.58/0.96    $false | (spl4_3 | ~spl4_25 | ~spl4_28)),
% 0.58/0.96    inference(unit_resulting_resolution,[],[f541,f87,f987,f66])).
% 0.58/0.96  fof(f987,plain,(
% 0.58/0.96    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_25),
% 0.58/0.96    inference(resolution,[],[f690,f72])).
% 0.58/0.96  fof(f690,plain,(
% 0.58/0.96    ( ! [X0] : (~r1_tarski(X0,X0) | r1_tarski(k1_xboole_0,X0)) ) | ~spl4_25),
% 0.58/0.96    inference(superposition,[],[f498,f449])).
% 0.58/0.96  fof(f498,plain,(
% 0.58/0.96    ( ! [X2] : (r1_tarski(k1_xboole_0,k2_xboole_0(X2,X2))) ) | ~spl4_25),
% 0.58/0.96    inference(avatar_component_clause,[],[f497])).
% 0.58/0.96  fof(f497,plain,(
% 0.58/0.96    spl4_25 <=> ! [X2] : r1_tarski(k1_xboole_0,k2_xboole_0(X2,X2))),
% 0.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.58/0.96  fof(f87,plain,(
% 0.58/0.96    k1_xboole_0 != sK2 | spl4_3),
% 0.58/0.96    inference(avatar_component_clause,[],[f85])).
% 0.58/0.96  fof(f85,plain,(
% 0.58/0.96    spl4_3 <=> k1_xboole_0 = sK2),
% 0.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.58/0.96  fof(f541,plain,(
% 0.58/0.96    r1_tarski(sK2,k1_xboole_0) | ~spl4_28),
% 0.58/0.96    inference(avatar_component_clause,[],[f539])).
% 0.58/0.98  % (19259)Time limit reached!
% 0.58/0.98  % (19259)------------------------------
% 0.58/0.98  % (19259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.58/0.98  % (19259)Termination reason: Time limit
% 0.58/0.98  % (19259)Termination phase: Saturation
% 0.58/0.98  
% 0.58/0.98  % (19259)Memory used [KB]: 13816
% 0.58/0.98  % (19259)Time elapsed: 0.400 s
% 0.58/0.98  % (19259)------------------------------
% 0.58/0.98  % (19259)------------------------------
% 0.58/0.98  fof(f539,plain,(
% 0.58/0.98    spl4_28 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.58/0.98    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.58/0.98  fof(f989,plain,(
% 0.58/0.98    spl4_15 | ~spl4_25),
% 0.58/0.98    inference(avatar_contradiction_clause,[],[f986])).
% 0.58/0.98  fof(f986,plain,(
% 0.58/0.98    $false | (spl4_15 | ~spl4_25)),
% 0.58/0.98    inference(unit_resulting_resolution,[],[f194,f72,f690])).
% 0.58/0.98  fof(f194,plain,(
% 0.58/0.98    ~r1_tarski(k1_xboole_0,sK1) | spl4_15),
% 0.58/0.98    inference(avatar_component_clause,[],[f192])).
% 0.58/0.98  fof(f809,plain,(
% 0.58/0.98    spl4_33 | ~spl4_7 | ~spl4_19),
% 0.58/0.98    inference(avatar_split_clause,[],[f655,f263,f108,f806])).
% 0.58/0.98  fof(f108,plain,(
% 0.58/0.98    spl4_7 <=> k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0))),
% 0.58/0.98    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.58/0.98  fof(f655,plain,(
% 0.58/0.98    k1_xboole_0 = k4_xboole_0(sK1,sK2) | (~spl4_7 | ~spl4_19)),
% 0.58/0.98    inference(superposition,[],[f110,f265])).
% 0.58/0.98  fof(f110,plain,(
% 0.58/0.98    k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_7),
% 0.58/0.98    inference(avatar_component_clause,[],[f108])).
% 0.58/0.98  fof(f582,plain,(
% 0.58/0.98    spl4_29 | ~spl4_6 | ~spl4_19),
% 0.58/0.98    inference(avatar_split_clause,[],[f552,f263,f101,f579])).
% 0.58/0.98  fof(f101,plain,(
% 0.58/0.98    spl4_6 <=> r1_tarski(sK1,k1_tarski(sK0))),
% 0.58/0.98    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.58/0.98  fof(f552,plain,(
% 0.58/0.98    r1_tarski(sK1,sK2) | (~spl4_6 | ~spl4_19)),
% 0.58/0.98    inference(superposition,[],[f103,f265])).
% 0.58/0.98  fof(f103,plain,(
% 0.58/0.98    r1_tarski(sK1,k1_tarski(sK0)) | ~spl4_6),
% 0.58/0.98    inference(avatar_component_clause,[],[f101])).
% 0.58/0.98  fof(f545,plain,(
% 0.58/0.98    spl4_20 | spl4_27),
% 0.58/0.98    inference(avatar_contradiction_clause,[],[f543])).
% 0.58/0.98  fof(f543,plain,(
% 0.58/0.98    $false | (spl4_20 | spl4_27)),
% 0.58/0.98    inference(unit_resulting_resolution,[],[f271,f537,f51])).
% 0.58/0.98  fof(f537,plain,(
% 0.58/0.98    ~r1_xboole_0(k1_tarski(sK0),sK2) | spl4_27),
% 0.58/0.98    inference(avatar_component_clause,[],[f535])).
% 0.58/0.98  fof(f535,plain,(
% 0.58/0.98    spl4_27 <=> r1_xboole_0(k1_tarski(sK0),sK2)),
% 0.58/0.98    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.58/0.98  fof(f271,plain,(
% 0.58/0.98    ~r2_hidden(sK0,sK2) | spl4_20),
% 0.58/0.98    inference(avatar_component_clause,[],[f269])).
% 0.58/0.98  fof(f269,plain,(
% 0.58/0.98    spl4_20 <=> r2_hidden(sK0,sK2)),
% 0.58/0.98    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.58/0.98  fof(f542,plain,(
% 0.58/0.98    ~spl4_27 | spl4_28 | ~spl4_4),
% 0.58/0.98    inference(avatar_split_clause,[],[f533,f90,f539,f535])).
% 0.58/0.98  fof(f90,plain,(
% 0.58/0.98    spl4_4 <=> k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 0.58/0.98    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.58/0.98  fof(f533,plain,(
% 0.58/0.98    r1_tarski(sK2,k1_xboole_0) | ~r1_xboole_0(k1_tarski(sK0),sK2) | ~spl4_4),
% 0.58/0.98    inference(superposition,[],[f521,f116])).
% 0.58/0.98  fof(f116,plain,(
% 0.58/0.98    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.58/0.98    inference(resolution,[],[f59,f43])).
% 0.58/0.98  fof(f43,plain,(
% 0.58/0.98    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.58/0.98    inference(cnf_transformation,[],[f24])).
% 0.58/0.98  fof(f24,plain,(
% 0.58/0.98    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.58/0.98    inference(ennf_transformation,[],[f8])).
% 0.58/0.98  fof(f8,axiom,(
% 0.58/0.98    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.58/0.98  fof(f59,plain,(
% 0.58/0.98    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.58/0.98    inference(cnf_transformation,[],[f11])).
% 0.58/0.98  fof(f11,axiom,(
% 0.58/0.98    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).
% 0.58/0.98  fof(f521,plain,(
% 0.58/0.98    ( ! [X7] : (r1_tarski(sK2,k4_xboole_0(k1_tarski(sK0),X7)) | ~r1_xboole_0(X7,sK2)) ) | ~spl4_4),
% 0.58/0.98    inference(superposition,[],[f186,f277])).
% 0.58/0.98  fof(f277,plain,(
% 0.58/0.98    ( ! [X11] : (k2_xboole_0(k4_xboole_0(sK1,X11),sK2) = k4_xboole_0(k1_tarski(sK0),X11) | ~r1_xboole_0(X11,sK2)) ) | ~spl4_4),
% 0.58/0.98    inference(superposition,[],[f57,f92])).
% 0.58/0.98  fof(f92,plain,(
% 0.58/0.98    k2_xboole_0(sK1,sK2) = k1_tarski(sK0) | ~spl4_4),
% 0.58/0.98    inference(avatar_component_clause,[],[f90])).
% 0.58/0.98  fof(f507,plain,(
% 0.58/0.98    spl4_26),
% 0.58/0.98    inference(avatar_contradiction_clause,[],[f504])).
% 0.58/0.98  fof(f504,plain,(
% 0.58/0.98    $false | spl4_26),
% 0.58/0.98    inference(unit_resulting_resolution,[],[f72,f502])).
% 0.58/0.98  fof(f502,plain,(
% 0.58/0.98    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl4_26),
% 0.58/0.98    inference(avatar_component_clause,[],[f500])).
% 0.58/0.98  fof(f500,plain,(
% 0.58/0.98    spl4_26 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.58/0.98    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.58/0.98  fof(f503,plain,(
% 0.58/0.98    spl4_25 | ~spl4_26 | ~spl4_4),
% 0.58/0.98    inference(avatar_split_clause,[],[f487,f90,f500,f497])).
% 0.58/0.98  fof(f487,plain,(
% 0.58/0.98    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | r1_tarski(k1_xboole_0,k2_xboole_0(X2,X2))) ) | ~spl4_4),
% 0.58/0.98    inference(superposition,[],[f380,f116])).
% 0.58/0.98  fof(f380,plain,(
% 0.58/0.98    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k4_xboole_0(X1,X0)) | r1_tarski(k1_xboole_0,k2_xboole_0(X0,X1))) ) | ~spl4_4),
% 0.58/0.98    inference(superposition,[],[f337,f46])).
% 0.58/0.98  fof(f337,plain,(
% 0.58/0.98    ( ! [X4,X3] : (r1_tarski(k1_xboole_0,k2_xboole_0(X3,X4)) | ~r1_tarski(k1_xboole_0,X4)) ) | ~spl4_4),
% 0.58/0.98    inference(superposition,[],[f56,f327])).
% 0.58/0.98  fof(f327,plain,(
% 0.58/0.98    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) ) | ~spl4_4),
% 0.58/0.98    inference(forward_demodulation,[],[f326,f302])).
% 0.58/0.98  fof(f302,plain,(
% 0.58/0.98    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),X6))) ) | ~spl4_4),
% 0.58/0.98    inference(superposition,[],[f41,f212])).
% 0.58/0.98  fof(f212,plain,(
% 0.58/0.98    ( ! [X11] : (k2_xboole_0(sK1,k2_xboole_0(sK2,X11)) = k2_xboole_0(k1_tarski(sK0),X11)) ) | ~spl4_4),
% 0.58/0.98    inference(superposition,[],[f44,f92])).
% 0.58/0.98  fof(f326,plain,(
% 0.58/0.98    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(X0,X1)))) ) | ~spl4_4),
% 0.58/0.98    inference(forward_demodulation,[],[f321,f44])).
% 0.58/0.98  fof(f321,plain,(
% 0.58/0.98    ( ! [X0,X1] : (k4_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),X0),X1)) = k4_xboole_0(k1_xboole_0,X1)) ) | ~spl4_4),
% 0.58/0.98    inference(superposition,[],[f45,f302])).
% 0.58/0.98  fof(f45,plain,(
% 0.58/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.58/0.98    inference(cnf_transformation,[],[f4])).
% 0.58/0.98  fof(f4,axiom,(
% 0.58/0.98    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.58/0.98  fof(f272,plain,(
% 0.58/0.98    ~spl4_20 | spl4_18),
% 0.58/0.98    inference(avatar_split_clause,[],[f267,f259,f269])).
% 0.58/0.98  fof(f259,plain,(
% 0.58/0.98    spl4_18 <=> r1_tarski(k1_tarski(sK0),sK2)),
% 0.58/0.98    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.58/0.98  fof(f267,plain,(
% 0.58/0.98    ~r2_hidden(sK0,sK2) | spl4_18),
% 0.58/0.98    inference(resolution,[],[f261,f50])).
% 0.58/0.98  fof(f50,plain,(
% 0.58/0.98    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.58/0.98    inference(cnf_transformation,[],[f32])).
% 0.58/0.98  fof(f32,plain,(
% 0.58/0.98    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.58/0.98    inference(nnf_transformation,[],[f20])).
% 0.58/0.98  fof(f20,axiom,(
% 0.58/0.98    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 0.58/0.98  fof(f261,plain,(
% 0.58/0.98    ~r1_tarski(k1_tarski(sK0),sK2) | spl4_18),
% 0.58/0.98    inference(avatar_component_clause,[],[f259])).
% 0.58/0.98  fof(f266,plain,(
% 0.58/0.98    ~spl4_18 | spl4_19 | ~spl4_17),
% 0.58/0.98    inference(avatar_split_clause,[],[f236,f232,f263,f259])).
% 0.58/0.98  fof(f232,plain,(
% 0.58/0.98    spl4_17 <=> r1_tarski(sK2,k1_tarski(sK0))),
% 0.58/0.98    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.58/0.98  fof(f236,plain,(
% 0.58/0.98    sK2 = k1_tarski(sK0) | ~r1_tarski(k1_tarski(sK0),sK2) | ~spl4_17),
% 0.58/0.98    inference(resolution,[],[f234,f66])).
% 0.58/0.98  fof(f234,plain,(
% 0.58/0.98    r1_tarski(sK2,k1_tarski(sK0)) | ~spl4_17),
% 0.58/0.98    inference(avatar_component_clause,[],[f232])).
% 0.58/0.98  fof(f235,plain,(
% 0.58/0.98    spl4_17 | ~spl4_4),
% 0.58/0.98    inference(avatar_split_clause,[],[f203,f90,f232])).
% 0.58/0.98  fof(f203,plain,(
% 0.58/0.98    r1_tarski(sK2,k1_tarski(sK0)) | ~spl4_4),
% 0.58/0.98    inference(superposition,[],[f186,f92])).
% 0.58/0.98  fof(f180,plain,(
% 0.58/0.98    ~spl4_14 | spl4_12),
% 0.58/0.98    inference(avatar_split_clause,[],[f175,f167,f177])).
% 0.58/0.98  fof(f167,plain,(
% 0.58/0.98    spl4_12 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 0.58/0.98    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.58/0.98  fof(f175,plain,(
% 0.58/0.98    ~r2_hidden(sK0,sK1) | spl4_12),
% 0.58/0.98    inference(resolution,[],[f169,f50])).
% 0.58/0.98  fof(f169,plain,(
% 0.58/0.98    ~r1_tarski(k1_tarski(sK0),sK1) | spl4_12),
% 0.58/0.98    inference(avatar_component_clause,[],[f167])).
% 0.58/0.98  fof(f174,plain,(
% 0.58/0.98    ~spl4_12 | spl4_13 | ~spl4_6),
% 0.58/0.98    inference(avatar_split_clause,[],[f164,f101,f171,f167])).
% 0.58/0.98  fof(f171,plain,(
% 0.58/0.98    spl4_13 <=> sK1 = k1_tarski(sK0)),
% 0.58/0.98    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.58/0.98  fof(f164,plain,(
% 0.58/0.98    sK1 = k1_tarski(sK0) | ~r1_tarski(k1_tarski(sK0),sK1) | ~spl4_6),
% 0.58/0.98    inference(resolution,[],[f66,f103])).
% 0.58/0.98  fof(f151,plain,(
% 0.58/0.98    spl4_11 | ~spl4_4),
% 0.58/0.98    inference(avatar_split_clause,[],[f141,f90,f148])).
% 0.58/0.98  fof(f141,plain,(
% 0.58/0.98    k1_tarski(sK0) = k2_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_4),
% 0.58/0.98    inference(superposition,[],[f47,f92])).
% 0.58/0.98  fof(f47,plain,(
% 0.58/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.58/0.98    inference(cnf_transformation,[],[f9])).
% 0.58/0.98  fof(f9,axiom,(
% 0.58/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 0.58/0.98  fof(f111,plain,(
% 0.58/0.98    spl4_7 | ~spl4_4),
% 0.58/0.98    inference(avatar_split_clause,[],[f106,f90,f108])).
% 0.58/0.98  fof(f106,plain,(
% 0.58/0.98    k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_4),
% 0.58/0.98    inference(superposition,[],[f41,f92])).
% 0.58/0.98  fof(f104,plain,(
% 0.58/0.98    spl4_6 | ~spl4_4),
% 0.58/0.98    inference(avatar_split_clause,[],[f99,f90,f101])).
% 0.58/0.98  fof(f99,plain,(
% 0.58/0.98    r1_tarski(sK1,k1_tarski(sK0)) | ~spl4_4),
% 0.58/0.98    inference(superposition,[],[f58,f92])).
% 0.58/0.98  fof(f58,plain,(
% 0.58/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.58/0.98    inference(cnf_transformation,[],[f10])).
% 0.58/0.98  fof(f10,axiom,(
% 0.58/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.58/0.98  fof(f93,plain,(
% 0.58/0.98    spl4_4),
% 0.58/0.98    inference(avatar_split_clause,[],[f37,f90])).
% 0.58/0.98  fof(f37,plain,(
% 0.58/0.98    k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 0.58/0.98    inference(cnf_transformation,[],[f31])).
% 0.58/0.98  fof(f31,plain,(
% 0.58/0.98    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 0.58/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f30])).
% 0.58/0.98  fof(f30,plain,(
% 0.58/0.98    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k2_xboole_0(sK1,sK2) = k1_tarski(sK0))),
% 0.58/0.98    introduced(choice_axiom,[])).
% 0.58/0.98  fof(f23,plain,(
% 0.58/0.98    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.58/0.98    inference(ennf_transformation,[],[f22])).
% 0.58/0.98  fof(f22,negated_conjecture,(
% 0.58/0.98    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.58/0.98    inference(negated_conjecture,[],[f21])).
% 0.58/0.98  fof(f21,conjecture,(
% 0.58/0.98    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.58/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.58/0.98  fof(f88,plain,(
% 0.58/0.98    ~spl4_3),
% 0.58/0.98    inference(avatar_split_clause,[],[f40,f85])).
% 0.58/0.98  fof(f40,plain,(
% 0.58/0.98    k1_xboole_0 != sK2),
% 0.58/0.98    inference(cnf_transformation,[],[f31])).
% 0.58/0.98  fof(f83,plain,(
% 0.58/0.98    ~spl4_2),
% 0.58/0.98    inference(avatar_split_clause,[],[f39,f80])).
% 0.58/0.98  fof(f39,plain,(
% 0.58/0.98    k1_xboole_0 != sK1),
% 0.58/0.98    inference(cnf_transformation,[],[f31])).
% 0.58/0.98  fof(f78,plain,(
% 0.58/0.98    ~spl4_1),
% 0.58/0.98    inference(avatar_split_clause,[],[f38,f75])).
% 0.58/0.98  fof(f75,plain,(
% 0.58/0.98    spl4_1 <=> sK1 = sK2),
% 0.58/0.98    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.58/0.98  fof(f38,plain,(
% 0.58/0.98    sK1 != sK2),
% 0.58/0.98    inference(cnf_transformation,[],[f31])).
% 0.58/0.98  % SZS output end Proof for theBenchmark
% 0.58/0.98  % (19258)------------------------------
% 0.58/0.98  % (19258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.58/0.98  % (19258)Termination reason: Refutation
% 0.58/0.98  
% 0.58/0.98  % (19258)Memory used [KB]: 14328
% 0.58/0.98  % (19258)Time elapsed: 0.398 s
% 0.58/0.98  % (19258)------------------------------
% 0.58/0.98  % (19258)------------------------------
% 0.58/0.99  % (19082)Success in time 0.624 s
%------------------------------------------------------------------------------

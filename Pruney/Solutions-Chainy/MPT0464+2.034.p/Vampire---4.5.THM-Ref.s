%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:29 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 177 expanded)
%              Number of leaves         :   18 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :  197 ( 513 expanded)
%              Number of equality atoms :   21 (  61 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1642,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f979,f1623,f1627,f1641])).

fof(f1641,plain,
    ( spl9_12
    | ~ spl9_22 ),
    inference(avatar_contradiction_clause,[],[f1640])).

fof(f1640,plain,
    ( $false
    | spl9_12
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f1639,f1613])).

fof(f1613,plain,
    ( v1_relat_1(k3_xboole_0(sK3,sK4))
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f1612])).

fof(f1612,plain,
    ( spl9_22
  <=> v1_relat_1(k3_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f1639,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK3,sK4))
    | spl9_12 ),
    inference(subsumption_resolution,[],[f1638,f77])).

fof(f77,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))
    & v1_relat_1(sK4)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f51,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK2,X1),k5_relat_1(sK2,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK2,X1),k5_relat_1(sK2,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,X2)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,X2)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(f1638,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(k3_xboole_0(sK3,sK4))
    | spl9_12 ),
    inference(subsumption_resolution,[],[f1637,f75])).

fof(f75,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f1637,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(k3_xboole_0(sK3,sK4))
    | spl9_12 ),
    inference(subsumption_resolution,[],[f1634,f1527])).

fof(f1527,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(forward_demodulation,[],[f1514,f1302])).

fof(f1302,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(subsumption_resolution,[],[f1294,f123])).

fof(f123,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1294,plain,(
    ! [X2] :
      ( k2_xboole_0(X2,k1_xboole_0) = X2
      | ~ r1_tarski(X2,X2) ) ),
    inference(superposition,[],[f89,f1276])).

fof(f1276,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f713,f83])).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f713,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0))
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f114,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f1514,plain,(
    ! [X2,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X2,X1),k1_xboole_0),X1) ),
    inference(backward_demodulation,[],[f1308,f1489])).

fof(f1489,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1485,f79])).

fof(f79,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1485,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k3_xboole_0(X2,k1_xboole_0))
      | k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f184,f1444])).

fof(f1444,plain,(
    ! [X4] : k1_xboole_0 = k2_xboole_0(k3_xboole_0(X4,k1_xboole_0),k3_xboole_0(X4,k1_xboole_0)) ),
    inference(resolution,[],[f1308,f82])).

fof(f184,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(k2_xboole_0(X10,X11),X10)
      | k2_xboole_0(X10,X11) = X10 ) ),
    inference(resolution,[],[f94,f83])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1308,plain,(
    ! [X2,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X2,k1_xboole_0)),X1) ),
    inference(superposition,[],[f112,f1302])).

fof(f112,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f1634,plain,
    ( ~ r1_tarski(k3_xboole_0(sK3,sK4),sK4)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(k3_xboole_0(sK3,sK4))
    | spl9_12 ),
    inference(resolution,[],[f978,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(f978,plain,
    ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k5_relat_1(sK2,sK4))
    | spl9_12 ),
    inference(avatar_component_clause,[],[f976])).

fof(f976,plain,
    ( spl9_12
  <=> r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k5_relat_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f1627,plain,(
    spl9_22 ),
    inference(avatar_contradiction_clause,[],[f1626])).

fof(f1626,plain,
    ( $false
    | spl9_22 ),
    inference(subsumption_resolution,[],[f1624,f76])).

fof(f76,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f1624,plain,
    ( ~ v1_relat_1(sK3)
    | spl9_22 ),
    inference(resolution,[],[f1614,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f1614,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK3,sK4))
    | spl9_22 ),
    inference(avatar_component_clause,[],[f1612])).

fof(f1623,plain,
    ( ~ spl9_22
    | spl9_11 ),
    inference(avatar_split_clause,[],[f1622,f972,f1612])).

fof(f972,plain,
    ( spl9_11
  <=> r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f1622,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK3,sK4))
    | spl9_11 ),
    inference(subsumption_resolution,[],[f1621,f76])).

fof(f1621,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k3_xboole_0(sK3,sK4))
    | spl9_11 ),
    inference(subsumption_resolution,[],[f1620,f75])).

fof(f1620,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k3_xboole_0(sK3,sK4))
    | spl9_11 ),
    inference(subsumption_resolution,[],[f1605,f85])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1605,plain,
    ( ~ r1_tarski(k3_xboole_0(sK3,sK4),sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k3_xboole_0(sK3,sK4))
    | spl9_11 ),
    inference(resolution,[],[f81,f974])).

fof(f974,plain,
    ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k5_relat_1(sK2,sK3))
    | spl9_11 ),
    inference(avatar_component_clause,[],[f972])).

fof(f979,plain,
    ( ~ spl9_11
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f965,f976,f972])).

fof(f965,plain,
    ( ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k5_relat_1(sK2,sK4))
    | ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k5_relat_1(sK2,sK3)) ),
    inference(resolution,[],[f116,f78])).

fof(f78,plain,(
    ~ r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4))) ),
    inference(cnf_transformation,[],[f52])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (30886)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (30878)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (30870)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (30877)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (30886)Refutation not found, incomplete strategy% (30886)------------------------------
% 0.20/0.51  % (30886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (30886)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (30886)Memory used [KB]: 10746
% 0.20/0.51  % (30886)Time elapsed: 0.061 s
% 0.20/0.51  % (30886)------------------------------
% 0.20/0.51  % (30886)------------------------------
% 0.20/0.51  % (30876)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (30868)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (30893)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (30869)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (30892)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (30883)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (30891)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (30885)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (30885)Refutation not found, incomplete strategy% (30885)------------------------------
% 0.20/0.53  % (30885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (30885)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (30885)Memory used [KB]: 1663
% 0.20/0.53  % (30885)Time elapsed: 0.123 s
% 0.20/0.53  % (30885)------------------------------
% 0.20/0.53  % (30885)------------------------------
% 0.20/0.53  % (30866)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (30865)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (30866)Refutation not found, incomplete strategy% (30866)------------------------------
% 0.20/0.53  % (30866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (30866)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (30866)Memory used [KB]: 10746
% 0.20/0.53  % (30866)Time elapsed: 0.127 s
% 0.20/0.53  % (30866)------------------------------
% 0.20/0.53  % (30866)------------------------------
% 0.20/0.53  % (30875)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (30890)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (30889)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (30867)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (30884)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (30864)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (30888)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (30881)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (30881)Refutation not found, incomplete strategy% (30881)------------------------------
% 0.20/0.54  % (30881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (30881)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (30881)Memory used [KB]: 10618
% 0.20/0.54  % (30881)Time elapsed: 0.139 s
% 0.20/0.54  % (30881)------------------------------
% 0.20/0.54  % (30881)------------------------------
% 0.20/0.54  % (30884)Refutation not found, incomplete strategy% (30884)------------------------------
% 0.20/0.54  % (30884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (30884)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (30884)Memory used [KB]: 10746
% 0.20/0.54  % (30884)Time elapsed: 0.143 s
% 0.20/0.54  % (30884)------------------------------
% 0.20/0.54  % (30884)------------------------------
% 0.20/0.54  % (30879)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (30873)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (30880)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (30871)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (30882)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (30874)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (30872)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (30887)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.56  % (30872)Refutation not found, incomplete strategy% (30872)------------------------------
% 0.20/0.56  % (30872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (30872)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (30872)Memory used [KB]: 10746
% 0.20/0.56  % (30872)Time elapsed: 0.151 s
% 0.20/0.56  % (30872)------------------------------
% 0.20/0.56  % (30872)------------------------------
% 1.84/0.61  % (30891)Refutation found. Thanks to Tanya!
% 1.84/0.61  % SZS status Theorem for theBenchmark
% 1.84/0.62  % SZS output start Proof for theBenchmark
% 1.84/0.62  fof(f1642,plain,(
% 1.84/0.62    $false),
% 1.84/0.62    inference(avatar_sat_refutation,[],[f979,f1623,f1627,f1641])).
% 1.84/0.62  fof(f1641,plain,(
% 1.84/0.62    spl9_12 | ~spl9_22),
% 1.84/0.62    inference(avatar_contradiction_clause,[],[f1640])).
% 1.84/0.62  fof(f1640,plain,(
% 1.84/0.62    $false | (spl9_12 | ~spl9_22)),
% 1.84/0.62    inference(subsumption_resolution,[],[f1639,f1613])).
% 1.84/0.62  fof(f1613,plain,(
% 1.84/0.62    v1_relat_1(k3_xboole_0(sK3,sK4)) | ~spl9_22),
% 1.84/0.62    inference(avatar_component_clause,[],[f1612])).
% 1.84/0.62  fof(f1612,plain,(
% 1.84/0.62    spl9_22 <=> v1_relat_1(k3_xboole_0(sK3,sK4))),
% 1.84/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 1.84/0.62  fof(f1639,plain,(
% 1.84/0.62    ~v1_relat_1(k3_xboole_0(sK3,sK4)) | spl9_12),
% 1.84/0.62    inference(subsumption_resolution,[],[f1638,f77])).
% 1.84/0.62  fof(f77,plain,(
% 1.84/0.62    v1_relat_1(sK4)),
% 1.84/0.62    inference(cnf_transformation,[],[f52])).
% 1.84/0.62  fof(f52,plain,(
% 1.84/0.62    ((~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4))) & v1_relat_1(sK4)) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 1.84/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f51,f50,f49])).
% 1.84/0.62  fof(f49,plain,(
% 1.84/0.62    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK2,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK2,X1),k5_relat_1(sK2,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 1.84/0.62    introduced(choice_axiom,[])).
% 1.84/0.62  fof(f50,plain,(
% 1.84/0.62    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK2,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK2,X1),k5_relat_1(sK2,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,X2)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,X2))) & v1_relat_1(X2)) & v1_relat_1(sK3))),
% 1.84/0.62    introduced(choice_axiom,[])).
% 1.84/0.62  fof(f51,plain,(
% 1.84/0.62    ? [X2] : (~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,X2)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4))) & v1_relat_1(sK4))),
% 1.84/0.62    introduced(choice_axiom,[])).
% 1.84/0.62  fof(f28,plain,(
% 1.84/0.62    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.84/0.62    inference(ennf_transformation,[],[f27])).
% 1.84/0.62  fof(f27,negated_conjecture,(
% 1.84/0.62    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.84/0.62    inference(negated_conjecture,[],[f26])).
% 1.84/0.62  fof(f26,conjecture,(
% 1.84/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).
% 1.84/0.62  fof(f1638,plain,(
% 1.84/0.62    ~v1_relat_1(sK4) | ~v1_relat_1(k3_xboole_0(sK3,sK4)) | spl9_12),
% 1.84/0.62    inference(subsumption_resolution,[],[f1637,f75])).
% 1.84/0.62  fof(f75,plain,(
% 1.84/0.62    v1_relat_1(sK2)),
% 1.84/0.62    inference(cnf_transformation,[],[f52])).
% 1.84/0.62  fof(f1637,plain,(
% 1.84/0.62    ~v1_relat_1(sK2) | ~v1_relat_1(sK4) | ~v1_relat_1(k3_xboole_0(sK3,sK4)) | spl9_12),
% 1.84/0.62    inference(subsumption_resolution,[],[f1634,f1527])).
% 1.84/0.62  fof(f1527,plain,(
% 1.84/0.62    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 1.84/0.62    inference(forward_demodulation,[],[f1514,f1302])).
% 1.84/0.62  fof(f1302,plain,(
% 1.84/0.62    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.84/0.62    inference(subsumption_resolution,[],[f1294,f123])).
% 1.84/0.62  fof(f123,plain,(
% 1.84/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.84/0.62    inference(equality_resolution,[],[f93])).
% 1.84/0.62  fof(f93,plain,(
% 1.84/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.84/0.62    inference(cnf_transformation,[],[f54])).
% 1.84/0.62  fof(f54,plain,(
% 1.84/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/0.62    inference(flattening,[],[f53])).
% 1.84/0.62  fof(f53,plain,(
% 1.84/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/0.62    inference(nnf_transformation,[],[f2])).
% 1.84/0.62  fof(f2,axiom,(
% 1.84/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.84/0.62  fof(f1294,plain,(
% 1.84/0.62    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2 | ~r1_tarski(X2,X2)) )),
% 1.84/0.62    inference(superposition,[],[f89,f1276])).
% 1.84/0.62  fof(f1276,plain,(
% 1.84/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.84/0.62    inference(resolution,[],[f713,f83])).
% 1.84/0.62  fof(f83,plain,(
% 1.84/0.62    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.84/0.62    inference(cnf_transformation,[],[f13])).
% 1.84/0.62  fof(f13,axiom,(
% 1.84/0.62    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.84/0.62  fof(f713,plain,(
% 1.84/0.62    ( ! [X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0)) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.84/0.62    inference(resolution,[],[f114,f82])).
% 1.84/0.62  fof(f82,plain,(
% 1.84/0.62    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.84/0.62    inference(cnf_transformation,[],[f31])).
% 1.84/0.62  fof(f31,plain,(
% 1.84/0.62    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.84/0.62    inference(ennf_transformation,[],[f10])).
% 1.84/0.62  fof(f10,axiom,(
% 1.84/0.62    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.84/0.62  fof(f114,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.84/0.62    inference(cnf_transformation,[],[f40])).
% 1.84/0.62  fof(f40,plain,(
% 1.84/0.62    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.84/0.62    inference(ennf_transformation,[],[f11])).
% 1.84/0.62  fof(f11,axiom,(
% 1.84/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.84/0.62  fof(f89,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f34])).
% 1.84/0.62  fof(f34,plain,(
% 1.84/0.62    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 1.84/0.62    inference(ennf_transformation,[],[f12])).
% 1.84/0.62  fof(f12,axiom,(
% 1.84/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 1.84/0.62  fof(f1514,plain,(
% 1.84/0.62    ( ! [X2,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X2,X1),k1_xboole_0),X1)) )),
% 1.84/0.62    inference(backward_demodulation,[],[f1308,f1489])).
% 1.84/0.62  fof(f1489,plain,(
% 1.84/0.62    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) )),
% 1.84/0.62    inference(subsumption_resolution,[],[f1485,f79])).
% 1.84/0.62  fof(f79,plain,(
% 1.84/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f6])).
% 1.84/0.62  fof(f6,axiom,(
% 1.84/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.84/0.62  fof(f1485,plain,(
% 1.84/0.62    ( ! [X2] : (~r1_tarski(k1_xboole_0,k3_xboole_0(X2,k1_xboole_0)) | k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) )),
% 1.84/0.62    inference(superposition,[],[f184,f1444])).
% 1.84/0.62  fof(f1444,plain,(
% 1.84/0.62    ( ! [X4] : (k1_xboole_0 = k2_xboole_0(k3_xboole_0(X4,k1_xboole_0),k3_xboole_0(X4,k1_xboole_0))) )),
% 1.84/0.62    inference(resolution,[],[f1308,f82])).
% 1.84/0.62  fof(f184,plain,(
% 1.84/0.62    ( ! [X10,X11] : (~r1_tarski(k2_xboole_0(X10,X11),X10) | k2_xboole_0(X10,X11) = X10) )),
% 1.84/0.62    inference(resolution,[],[f94,f83])).
% 1.84/0.62  fof(f94,plain,(
% 1.84/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f54])).
% 1.84/0.62  fof(f1308,plain,(
% 1.84/0.62    ( ! [X2,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X2,k1_xboole_0)),X1)) )),
% 1.84/0.62    inference(superposition,[],[f112,f1302])).
% 1.84/0.62  fof(f112,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 1.84/0.62    inference(cnf_transformation,[],[f7])).
% 1.84/0.62  fof(f7,axiom,(
% 1.84/0.62    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 1.84/0.62  fof(f1634,plain,(
% 1.84/0.62    ~r1_tarski(k3_xboole_0(sK3,sK4),sK4) | ~v1_relat_1(sK2) | ~v1_relat_1(sK4) | ~v1_relat_1(k3_xboole_0(sK3,sK4)) | spl9_12),
% 1.84/0.62    inference(resolution,[],[f978,f81])).
% 1.84/0.62  fof(f81,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f30])).
% 1.84/0.62  fof(f30,plain,(
% 1.84/0.62    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.84/0.62    inference(flattening,[],[f29])).
% 1.84/0.62  fof(f29,plain,(
% 1.84/0.62    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.84/0.62    inference(ennf_transformation,[],[f25])).
% 1.84/0.62  fof(f25,axiom,(
% 1.84/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).
% 1.84/0.62  fof(f978,plain,(
% 1.84/0.62    ~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k5_relat_1(sK2,sK4)) | spl9_12),
% 1.84/0.62    inference(avatar_component_clause,[],[f976])).
% 1.84/0.62  fof(f976,plain,(
% 1.84/0.62    spl9_12 <=> r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k5_relat_1(sK2,sK4))),
% 1.84/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.84/0.62  fof(f1627,plain,(
% 1.84/0.62    spl9_22),
% 1.84/0.62    inference(avatar_contradiction_clause,[],[f1626])).
% 1.84/0.62  fof(f1626,plain,(
% 1.84/0.62    $false | spl9_22),
% 1.84/0.62    inference(subsumption_resolution,[],[f1624,f76])).
% 1.84/0.62  fof(f76,plain,(
% 1.84/0.62    v1_relat_1(sK3)),
% 1.84/0.62    inference(cnf_transformation,[],[f52])).
% 1.84/0.62  fof(f1624,plain,(
% 1.84/0.62    ~v1_relat_1(sK3) | spl9_22),
% 1.84/0.62    inference(resolution,[],[f1614,f87])).
% 1.84/0.62  fof(f87,plain,(
% 1.84/0.62    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f32])).
% 1.84/0.62  fof(f32,plain,(
% 1.84/0.62    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.84/0.62    inference(ennf_transformation,[],[f24])).
% 1.84/0.62  fof(f24,axiom,(
% 1.84/0.62    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 1.84/0.62  fof(f1614,plain,(
% 1.84/0.62    ~v1_relat_1(k3_xboole_0(sK3,sK4)) | spl9_22),
% 1.84/0.62    inference(avatar_component_clause,[],[f1612])).
% 1.84/0.62  fof(f1623,plain,(
% 1.84/0.62    ~spl9_22 | spl9_11),
% 1.84/0.62    inference(avatar_split_clause,[],[f1622,f972,f1612])).
% 1.84/0.62  fof(f972,plain,(
% 1.84/0.62    spl9_11 <=> r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k5_relat_1(sK2,sK3))),
% 1.84/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.84/0.62  fof(f1622,plain,(
% 1.84/0.62    ~v1_relat_1(k3_xboole_0(sK3,sK4)) | spl9_11),
% 1.84/0.62    inference(subsumption_resolution,[],[f1621,f76])).
% 1.84/0.62  fof(f1621,plain,(
% 1.84/0.62    ~v1_relat_1(sK3) | ~v1_relat_1(k3_xboole_0(sK3,sK4)) | spl9_11),
% 1.84/0.62    inference(subsumption_resolution,[],[f1620,f75])).
% 1.84/0.62  fof(f1620,plain,(
% 1.84/0.62    ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k3_xboole_0(sK3,sK4)) | spl9_11),
% 1.84/0.62    inference(subsumption_resolution,[],[f1605,f85])).
% 1.84/0.62  fof(f85,plain,(
% 1.84/0.62    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f4])).
% 1.84/0.62  fof(f4,axiom,(
% 1.84/0.62    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.84/0.62  fof(f1605,plain,(
% 1.84/0.62    ~r1_tarski(k3_xboole_0(sK3,sK4),sK3) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k3_xboole_0(sK3,sK4)) | spl9_11),
% 1.84/0.62    inference(resolution,[],[f81,f974])).
% 1.84/0.62  fof(f974,plain,(
% 1.84/0.62    ~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k5_relat_1(sK2,sK3)) | spl9_11),
% 1.84/0.62    inference(avatar_component_clause,[],[f972])).
% 1.84/0.62  fof(f979,plain,(
% 1.84/0.62    ~spl9_11 | ~spl9_12),
% 1.84/0.62    inference(avatar_split_clause,[],[f965,f976,f972])).
% 1.84/0.62  fof(f965,plain,(
% 1.84/0.62    ~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k5_relat_1(sK2,sK4)) | ~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k5_relat_1(sK2,sK3))),
% 1.84/0.62    inference(resolution,[],[f116,f78])).
% 1.84/0.62  fof(f78,plain,(
% 1.84/0.62    ~r1_tarski(k5_relat_1(sK2,k3_xboole_0(sK3,sK4)),k3_xboole_0(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK4)))),
% 1.84/0.62    inference(cnf_transformation,[],[f52])).
% 1.84/0.62  fof(f116,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f44])).
% 1.84/0.62  fof(f44,plain,(
% 1.84/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.84/0.62    inference(flattening,[],[f43])).
% 1.84/0.62  fof(f43,plain,(
% 1.84/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.84/0.62    inference(ennf_transformation,[],[f5])).
% 1.84/0.62  fof(f5,axiom,(
% 1.84/0.62    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.84/0.62  % SZS output end Proof for theBenchmark
% 1.84/0.62  % (30891)------------------------------
% 1.84/0.62  % (30891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.62  % (30891)Termination reason: Refutation
% 1.84/0.62  
% 1.84/0.62  % (30891)Memory used [KB]: 6908
% 1.84/0.62  % (30891)Time elapsed: 0.201 s
% 1.84/0.62  % (30891)------------------------------
% 1.84/0.62  % (30891)------------------------------
% 1.84/0.63  % (30863)Success in time 0.262 s
%------------------------------------------------------------------------------

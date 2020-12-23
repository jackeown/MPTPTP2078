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
% DateTime   : Thu Dec  3 12:49:05 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 619 expanded)
%              Number of leaves         :   49 ( 235 expanded)
%              Depth                    :   16
%              Number of atoms          :  655 (2007 expanded)
%              Number of equality atoms :   36 ( 115 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f55,f60,f75,f80,f98,f103,f122,f127,f143,f148,f308,f311,f313,f353,f369,f377,f380,f382,f440,f458,f461,f463,f522,f549,f552,f554,f614,f628,f652,f666,f684,f687,f689,f752,f777,f791,f817,f820,f822,f889,f1134,f1137,f1139])).

fof(f1139,plain,
    ( ~ spl6_1
    | spl6_40 ),
    inference(avatar_contradiction_clause,[],[f1138])).

fof(f1138,plain,
    ( $false
    | ~ spl6_1
    | spl6_40 ),
    inference(subsumption_resolution,[],[f1136,f39])).

fof(f39,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl6_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1136,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_40 ),
    inference(resolution,[],[f1133,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f1133,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),sK2)
    | spl6_40 ),
    inference(avatar_component_clause,[],[f1131])).

fof(f1131,plain,
    ( spl6_40
  <=> r1_tarski(k8_relat_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f1137,plain,
    ( ~ spl6_1
    | spl6_40 ),
    inference(avatar_contradiction_clause,[],[f1135])).

fof(f1135,plain,
    ( $false
    | ~ spl6_1
    | spl6_40 ),
    inference(unit_resulting_resolution,[],[f39,f1133,f33])).

fof(f1134,plain,
    ( ~ spl6_40
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_14
    | spl6_17 ),
    inference(avatar_split_clause,[],[f1128,f366,f302,f47,f37,f1131])).

fof(f47,plain,
    ( spl6_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f302,plain,
    ( spl6_14
  <=> v1_relat_1(k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f366,plain,
    ( spl6_17
  <=> r1_tarski(k8_relat_1(sK0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f1128,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),sK2)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_14
    | spl6_17 ),
    inference(subsumption_resolution,[],[f1122,f303])).

fof(f303,plain,
    ( v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f302])).

fof(f1122,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ r1_tarski(k8_relat_1(sK0,sK2),sK2)
    | ~ spl6_1
    | ~ spl6_3
    | spl6_17 ),
    inference(resolution,[],[f1120,f368])).

fof(f368,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),sK3)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f366])).

fof(f1120,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK3)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,sK2) )
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(duplicate_literal_removal,[],[f1118])).

fof(f1118,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK3)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,sK2)
        | r1_tarski(X0,sK3)
        | ~ v1_relat_1(X0) )
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(resolution,[],[f1117,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f1117,plain,
    ( ! [X62,X63] :
        ( r2_hidden(k4_tarski(sK4(X62,X63),sK5(X62,X63)),sK3)
        | r1_tarski(X62,X63)
        | ~ v1_relat_1(X62)
        | ~ r1_tarski(X62,sK2) )
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f1097,f39])).

fof(f1097,plain,
    ( ! [X62,X63] :
        ( ~ v1_relat_1(X62)
        | r1_tarski(X62,X63)
        | r2_hidden(k4_tarski(sK4(X62,X63),sK5(X62,X63)),sK3)
        | ~ r1_tarski(X62,sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_3 ),
    inference(resolution,[],[f217,f49])).

fof(f49,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f217,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | ~ v1_relat_1(X2)
      | r1_tarski(X2,X4)
      | r2_hidden(k4_tarski(sK4(X2,X4),sK5(X2,X4)),X5)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f90,f29])).

fof(f29,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X5),X0)
      | r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2)
      | ~ r1_tarski(X0,X2)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2)
      | ~ r1_tarski(X0,X2)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f29,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f889,plain,
    ( ~ spl6_37
    | spl6_39
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f154,f145,f887,f811])).

fof(f811,plain,
    ( spl6_37
  <=> v1_relat_1(k8_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f887,plain,
    ( spl6_39
  <=> ! [X1] :
        ( r1_tarski(k8_relat_1(sK3,sK3),k8_relat_1(sK3,X1))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k8_relat_1(sK3,sK3),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f145,plain,
    ( spl6_13
  <=> k8_relat_1(sK3,sK3) = k8_relat_1(sK3,k8_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f154,plain,
    ( ! [X1] :
        ( r1_tarski(k8_relat_1(sK3,sK3),k8_relat_1(sK3,X1))
        | ~ r1_tarski(k8_relat_1(sK3,sK3),X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k8_relat_1(sK3,sK3)) )
    | ~ spl6_13 ),
    inference(superposition,[],[f34,f147])).

fof(f147,plain,
    ( k8_relat_1(sK3,sK3) = k8_relat_1(sK3,k8_relat_1(sK3,sK3))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

fof(f822,plain,
    ( ~ spl6_2
    | spl6_37 ),
    inference(avatar_contradiction_clause,[],[f821])).

fof(f821,plain,
    ( $false
    | ~ spl6_2
    | spl6_37 ),
    inference(subsumption_resolution,[],[f819,f44])).

fof(f44,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl6_2
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f819,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_37 ),
    inference(resolution,[],[f813,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f813,plain,
    ( ~ v1_relat_1(k8_relat_1(sK3,sK3))
    | spl6_37 ),
    inference(avatar_component_clause,[],[f811])).

fof(f820,plain,
    ( ~ spl6_2
    | spl6_37 ),
    inference(avatar_contradiction_clause,[],[f818])).

fof(f818,plain,
    ( $false
    | ~ spl6_2
    | spl6_37 ),
    inference(unit_resulting_resolution,[],[f44,f813,f32])).

fof(f817,plain,
    ( ~ spl6_37
    | spl6_38
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f153,f145,f815,f811])).

fof(f815,plain,
    ( spl6_38
  <=> ! [X0] :
        ( r1_tarski(k8_relat_1(sK3,X0),k8_relat_1(sK3,sK3))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,k8_relat_1(sK3,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f153,plain,
    ( ! [X0] :
        ( r1_tarski(k8_relat_1(sK3,X0),k8_relat_1(sK3,sK3))
        | ~ r1_tarski(X0,k8_relat_1(sK3,sK3))
        | ~ v1_relat_1(k8_relat_1(sK3,sK3))
        | ~ v1_relat_1(X0) )
    | ~ spl6_13 ),
    inference(superposition,[],[f34,f147])).

fof(f791,plain,
    ( ~ spl6_24
    | spl6_36
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f150,f140,f789,f543])).

fof(f543,plain,
    ( spl6_24
  <=> v1_relat_1(k8_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f789,plain,
    ( spl6_36
  <=> ! [X1] :
        ( r1_tarski(k8_relat_1(sK2,sK3),k8_relat_1(sK2,X1))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k8_relat_1(sK2,sK3),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f140,plain,
    ( spl6_12
  <=> k8_relat_1(sK2,sK3) = k8_relat_1(sK2,k8_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f150,plain,
    ( ! [X1] :
        ( r1_tarski(k8_relat_1(sK2,sK3),k8_relat_1(sK2,X1))
        | ~ r1_tarski(k8_relat_1(sK2,sK3),X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k8_relat_1(sK2,sK3)) )
    | ~ spl6_12 ),
    inference(superposition,[],[f34,f142])).

fof(f142,plain,
    ( k8_relat_1(sK2,sK3) = k8_relat_1(sK2,k8_relat_1(sK2,sK3))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f777,plain,
    ( ~ spl6_24
    | spl6_35
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f149,f140,f775,f543])).

fof(f775,plain,
    ( spl6_35
  <=> ! [X0] :
        ( r1_tarski(k8_relat_1(sK2,X0),k8_relat_1(sK2,sK3))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,k8_relat_1(sK2,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f149,plain,
    ( ! [X0] :
        ( r1_tarski(k8_relat_1(sK2,X0),k8_relat_1(sK2,sK3))
        | ~ r1_tarski(X0,k8_relat_1(sK2,sK3))
        | ~ v1_relat_1(k8_relat_1(sK2,sK3))
        | ~ v1_relat_1(X0) )
    | ~ spl6_12 ),
    inference(superposition,[],[f34,f142])).

fof(f752,plain,
    ( ~ spl6_32
    | spl6_34
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f133,f124,f750,f678])).

fof(f678,plain,
    ( spl6_32
  <=> v1_relat_1(k8_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f750,plain,
    ( spl6_34
  <=> ! [X1] :
        ( r1_tarski(k8_relat_1(sK3,sK2),k8_relat_1(sK3,X1))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k8_relat_1(sK3,sK2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f124,plain,
    ( spl6_11
  <=> k8_relat_1(sK3,sK2) = k8_relat_1(sK3,k8_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f133,plain,
    ( ! [X1] :
        ( r1_tarski(k8_relat_1(sK3,sK2),k8_relat_1(sK3,X1))
        | ~ r1_tarski(k8_relat_1(sK3,sK2),X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k8_relat_1(sK3,sK2)) )
    | ~ spl6_11 ),
    inference(superposition,[],[f34,f126])).

fof(f126,plain,
    ( k8_relat_1(sK3,sK2) = k8_relat_1(sK3,k8_relat_1(sK3,sK2))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f124])).

fof(f689,plain,
    ( ~ spl6_1
    | spl6_32 ),
    inference(avatar_contradiction_clause,[],[f688])).

fof(f688,plain,
    ( $false
    | ~ spl6_1
    | spl6_32 ),
    inference(subsumption_resolution,[],[f686,f39])).

fof(f686,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_32 ),
    inference(resolution,[],[f680,f32])).

fof(f680,plain,
    ( ~ v1_relat_1(k8_relat_1(sK3,sK2))
    | spl6_32 ),
    inference(avatar_component_clause,[],[f678])).

fof(f687,plain,
    ( ~ spl6_1
    | spl6_32 ),
    inference(avatar_contradiction_clause,[],[f685])).

fof(f685,plain,
    ( $false
    | ~ spl6_1
    | spl6_32 ),
    inference(unit_resulting_resolution,[],[f39,f680,f32])).

fof(f684,plain,
    ( ~ spl6_32
    | spl6_33
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f132,f124,f682,f678])).

fof(f682,plain,
    ( spl6_33
  <=> ! [X0] :
        ( r1_tarski(k8_relat_1(sK3,X0),k8_relat_1(sK3,sK2))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,k8_relat_1(sK3,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f132,plain,
    ( ! [X0] :
        ( r1_tarski(k8_relat_1(sK3,X0),k8_relat_1(sK3,sK2))
        | ~ r1_tarski(X0,k8_relat_1(sK3,sK2))
        | ~ v1_relat_1(k8_relat_1(sK3,sK2))
        | ~ v1_relat_1(X0) )
    | ~ spl6_11 ),
    inference(superposition,[],[f34,f126])).

fof(f666,plain,
    ( ~ spl6_21
    | spl6_31
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f129,f119,f664,f452])).

fof(f452,plain,
    ( spl6_21
  <=> v1_relat_1(k8_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f664,plain,
    ( spl6_31
  <=> ! [X1] :
        ( r1_tarski(k8_relat_1(sK2,sK2),k8_relat_1(sK2,X1))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k8_relat_1(sK2,sK2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f119,plain,
    ( spl6_10
  <=> k8_relat_1(sK2,sK2) = k8_relat_1(sK2,k8_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f129,plain,
    ( ! [X1] :
        ( r1_tarski(k8_relat_1(sK2,sK2),k8_relat_1(sK2,X1))
        | ~ r1_tarski(k8_relat_1(sK2,sK2),X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k8_relat_1(sK2,sK2)) )
    | ~ spl6_10 ),
    inference(superposition,[],[f34,f121])).

fof(f121,plain,
    ( k8_relat_1(sK2,sK2) = k8_relat_1(sK2,k8_relat_1(sK2,sK2))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f652,plain,
    ( ~ spl6_21
    | spl6_30
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f128,f119,f650,f452])).

fof(f650,plain,
    ( spl6_30
  <=> ! [X0] :
        ( r1_tarski(k8_relat_1(sK2,X0),k8_relat_1(sK2,sK2))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,k8_relat_1(sK2,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f128,plain,
    ( ! [X0] :
        ( r1_tarski(k8_relat_1(sK2,X0),k8_relat_1(sK2,sK2))
        | ~ r1_tarski(X0,k8_relat_1(sK2,sK2))
        | ~ v1_relat_1(k8_relat_1(sK2,sK2))
        | ~ v1_relat_1(X0) )
    | ~ spl6_10 ),
    inference(superposition,[],[f34,f121])).

fof(f628,plain,
    ( ~ spl6_24
    | spl6_29
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f109,f100,f626,f543])).

fof(f626,plain,
    ( spl6_29
  <=> ! [X1] :
        ( r1_tarski(k8_relat_1(sK2,sK3),k8_relat_1(sK3,X1))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k8_relat_1(sK2,sK3),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f100,plain,
    ( spl6_9
  <=> k8_relat_1(sK2,sK3) = k8_relat_1(sK3,k8_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f109,plain,
    ( ! [X1] :
        ( r1_tarski(k8_relat_1(sK2,sK3),k8_relat_1(sK3,X1))
        | ~ r1_tarski(k8_relat_1(sK2,sK3),X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k8_relat_1(sK2,sK3)) )
    | ~ spl6_9 ),
    inference(superposition,[],[f34,f102])).

fof(f102,plain,
    ( k8_relat_1(sK2,sK3) = k8_relat_1(sK3,k8_relat_1(sK2,sK3))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f614,plain,
    ( ~ spl6_26
    | ~ spl6_27
    | spl6_28
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f266,f52,f612,f608,f604])).

fof(f604,plain,
    ( spl6_26
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f608,plain,
    ( spl6_27
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f612,plain,
    ( spl6_28
  <=> ! [X13,X12] :
        ( ~ v1_relat_1(X12)
        | k8_relat_1(k8_relat_1(X13,sK0),X12) = k8_relat_1(k8_relat_1(X13,sK1),k8_relat_1(k8_relat_1(X13,sK0),X12)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f52,plain,
    ( spl6_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f266,plain,
    ( ! [X12,X13] :
        ( ~ v1_relat_1(X12)
        | k8_relat_1(k8_relat_1(X13,sK0),X12) = k8_relat_1(k8_relat_1(X13,sK1),k8_relat_1(k8_relat_1(X13,sK0),X12))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(sK0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f65,f54])).

fof(f54,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f65,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r1_tarski(X6,X8)
      | ~ v1_relat_1(X7)
      | k8_relat_1(k8_relat_1(X5,X6),X7) = k8_relat_1(k8_relat_1(X5,X8),k8_relat_1(k8_relat_1(X5,X6),X7))
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f35,f34])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(f554,plain,
    ( ~ spl6_2
    | spl6_24 ),
    inference(avatar_contradiction_clause,[],[f553])).

fof(f553,plain,
    ( $false
    | ~ spl6_2
    | spl6_24 ),
    inference(subsumption_resolution,[],[f551,f44])).

fof(f551,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_24 ),
    inference(resolution,[],[f545,f32])).

fof(f545,plain,
    ( ~ v1_relat_1(k8_relat_1(sK2,sK3))
    | spl6_24 ),
    inference(avatar_component_clause,[],[f543])).

fof(f552,plain,
    ( ~ spl6_2
    | spl6_24 ),
    inference(avatar_contradiction_clause,[],[f550])).

fof(f550,plain,
    ( $false
    | ~ spl6_2
    | spl6_24 ),
    inference(unit_resulting_resolution,[],[f44,f545,f32])).

fof(f549,plain,
    ( ~ spl6_24
    | spl6_25
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f108,f100,f547,f543])).

fof(f547,plain,
    ( spl6_25
  <=> ! [X0] :
        ( r1_tarski(k8_relat_1(sK3,X0),k8_relat_1(sK2,sK3))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,k8_relat_1(sK2,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f108,plain,
    ( ! [X0] :
        ( r1_tarski(k8_relat_1(sK3,X0),k8_relat_1(sK2,sK3))
        | ~ r1_tarski(X0,k8_relat_1(sK2,sK3))
        | ~ v1_relat_1(k8_relat_1(sK2,sK3))
        | ~ v1_relat_1(X0) )
    | ~ spl6_9 ),
    inference(superposition,[],[f34,f102])).

fof(f522,plain,
    ( ~ spl6_21
    | spl6_23
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f105,f95,f520,f452])).

fof(f520,plain,
    ( spl6_23
  <=> ! [X1] :
        ( r1_tarski(k8_relat_1(sK2,sK2),k8_relat_1(sK3,X1))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k8_relat_1(sK2,sK2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f95,plain,
    ( spl6_8
  <=> k8_relat_1(sK2,sK2) = k8_relat_1(sK3,k8_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f105,plain,
    ( ! [X1] :
        ( r1_tarski(k8_relat_1(sK2,sK2),k8_relat_1(sK3,X1))
        | ~ r1_tarski(k8_relat_1(sK2,sK2),X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k8_relat_1(sK2,sK2)) )
    | ~ spl6_8 ),
    inference(superposition,[],[f34,f97])).

fof(f97,plain,
    ( k8_relat_1(sK2,sK2) = k8_relat_1(sK3,k8_relat_1(sK2,sK2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f463,plain,
    ( ~ spl6_1
    | spl6_21 ),
    inference(avatar_contradiction_clause,[],[f462])).

fof(f462,plain,
    ( $false
    | ~ spl6_1
    | spl6_21 ),
    inference(subsumption_resolution,[],[f460,f39])).

fof(f460,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_21 ),
    inference(resolution,[],[f454,f32])).

fof(f454,plain,
    ( ~ v1_relat_1(k8_relat_1(sK2,sK2))
    | spl6_21 ),
    inference(avatar_component_clause,[],[f452])).

fof(f461,plain,
    ( ~ spl6_1
    | spl6_21 ),
    inference(avatar_contradiction_clause,[],[f459])).

fof(f459,plain,
    ( $false
    | ~ spl6_1
    | spl6_21 ),
    inference(unit_resulting_resolution,[],[f39,f454,f32])).

fof(f458,plain,
    ( ~ spl6_21
    | spl6_22
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f104,f95,f456,f452])).

fof(f456,plain,
    ( spl6_22
  <=> ! [X0] :
        ( r1_tarski(k8_relat_1(sK3,X0),k8_relat_1(sK2,sK2))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,k8_relat_1(sK2,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f104,plain,
    ( ! [X0] :
        ( r1_tarski(k8_relat_1(sK3,X0),k8_relat_1(sK2,sK2))
        | ~ r1_tarski(X0,k8_relat_1(sK2,sK2))
        | ~ v1_relat_1(k8_relat_1(sK2,sK2))
        | ~ v1_relat_1(X0) )
    | ~ spl6_8 ),
    inference(superposition,[],[f34,f97])).

fof(f440,plain,
    ( ~ spl6_18
    | spl6_20
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f86,f77,f438,f371])).

fof(f371,plain,
    ( spl6_18
  <=> v1_relat_1(k8_relat_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f438,plain,
    ( spl6_20
  <=> ! [X1] :
        ( r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,X1))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k8_relat_1(sK0,sK3),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f77,plain,
    ( spl6_7
  <=> k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f86,plain,
    ( ! [X1] :
        ( r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,X1))
        | ~ r1_tarski(k8_relat_1(sK0,sK3),X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k8_relat_1(sK0,sK3)) )
    | ~ spl6_7 ),
    inference(superposition,[],[f34,f79])).

fof(f79,plain,
    ( k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f382,plain,
    ( ~ spl6_2
    | spl6_18 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl6_2
    | spl6_18 ),
    inference(subsumption_resolution,[],[f379,f44])).

fof(f379,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_18 ),
    inference(resolution,[],[f373,f32])).

fof(f373,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK3))
    | spl6_18 ),
    inference(avatar_component_clause,[],[f371])).

fof(f380,plain,
    ( ~ spl6_2
    | spl6_18 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | ~ spl6_2
    | spl6_18 ),
    inference(unit_resulting_resolution,[],[f44,f373,f32])).

fof(f377,plain,
    ( ~ spl6_18
    | spl6_19
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f85,f77,f375,f371])).

fof(f375,plain,
    ( spl6_19
  <=> ! [X0] :
        ( r1_tarski(k8_relat_1(sK1,X0),k8_relat_1(sK0,sK3))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,k8_relat_1(sK0,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f85,plain,
    ( ! [X0] :
        ( r1_tarski(k8_relat_1(sK1,X0),k8_relat_1(sK0,sK3))
        | ~ r1_tarski(X0,k8_relat_1(sK0,sK3))
        | ~ v1_relat_1(k8_relat_1(sK0,sK3))
        | ~ v1_relat_1(X0) )
    | ~ spl6_7 ),
    inference(superposition,[],[f34,f79])).

fof(f369,plain,
    ( ~ spl6_17
    | ~ spl6_2
    | spl6_5
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f362,f351,f57,f42,f366])).

fof(f57,plain,
    ( spl6_5
  <=> r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f351,plain,
    ( spl6_16
  <=> ! [X1] :
        ( r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X1))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k8_relat_1(sK0,sK2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f362,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),sK3)
    | ~ spl6_2
    | spl6_5
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f354,f44])).

fof(f354,plain,
    ( ~ v1_relat_1(sK3)
    | ~ r1_tarski(k8_relat_1(sK0,sK2),sK3)
    | spl6_5
    | ~ spl6_16 ),
    inference(resolution,[],[f352,f59])).

fof(f59,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f352,plain,
    ( ! [X1] :
        ( r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X1))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k8_relat_1(sK0,sK2),X1) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f351])).

fof(f353,plain,
    ( ~ spl6_14
    | spl6_16
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f82,f72,f351,f302])).

fof(f72,plain,
    ( spl6_6
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f82,plain,
    ( ! [X1] :
        ( r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X1))
        | ~ r1_tarski(k8_relat_1(sK0,sK2),X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k8_relat_1(sK0,sK2)) )
    | ~ spl6_6 ),
    inference(superposition,[],[f34,f74])).

fof(f74,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f313,plain,
    ( ~ spl6_1
    | spl6_14 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | ~ spl6_1
    | spl6_14 ),
    inference(subsumption_resolution,[],[f310,f39])).

fof(f310,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_14 ),
    inference(resolution,[],[f304,f32])).

fof(f304,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f302])).

fof(f311,plain,
    ( ~ spl6_1
    | spl6_14 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl6_1
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f39,f304,f32])).

fof(f308,plain,
    ( ~ spl6_14
    | spl6_15
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f81,f72,f306,f302])).

fof(f306,plain,
    ( spl6_15
  <=> ! [X0] :
        ( r1_tarski(k8_relat_1(sK1,X0),k8_relat_1(sK0,sK2))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,k8_relat_1(sK0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f81,plain,
    ( ! [X0] :
        ( r1_tarski(k8_relat_1(sK1,X0),k8_relat_1(sK0,sK2))
        | ~ r1_tarski(X0,k8_relat_1(sK0,sK2))
        | ~ v1_relat_1(k8_relat_1(sK0,sK2))
        | ~ v1_relat_1(X0) )
    | ~ spl6_6 ),
    inference(superposition,[],[f34,f74])).

fof(f148,plain,
    ( spl6_13
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f137,f42,f145])).

fof(f137,plain,
    ( k8_relat_1(sK3,sK3) = k8_relat_1(sK3,k8_relat_1(sK3,sK3))
    | ~ spl6_2 ),
    inference(resolution,[],[f113,f44])).

fof(f113,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X1,sK3) = k8_relat_1(X1,k8_relat_1(X1,sK3)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f63,f44])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f35,f62])).

fof(f62,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f31,f30])).

fof(f143,plain,
    ( spl6_12
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f136,f42,f37,f140])).

fof(f136,plain,
    ( k8_relat_1(sK2,sK3) = k8_relat_1(sK2,k8_relat_1(sK2,sK3))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f113,f39])).

fof(f127,plain,
    ( spl6_11
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f116,f42,f37,f124])).

fof(f116,plain,
    ( k8_relat_1(sK3,sK2) = k8_relat_1(sK3,k8_relat_1(sK3,sK2))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f112,f44])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f63,f39])).

fof(f122,plain,
    ( spl6_10
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f115,f37,f119])).

fof(f115,plain,
    ( k8_relat_1(sK2,sK2) = k8_relat_1(sK2,k8_relat_1(sK2,sK2))
    | ~ spl6_1 ),
    inference(resolution,[],[f112,f39])).

fof(f103,plain,
    ( spl6_9
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f92,f47,f42,f100])).

fof(f92,plain,
    ( k8_relat_1(sK2,sK3) = k8_relat_1(sK3,k8_relat_1(sK2,sK3))
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f67,f44])).

fof(f67,plain,
    ( ! [X10] :
        ( ~ v1_relat_1(X10)
        | k8_relat_1(sK2,X10) = k8_relat_1(sK3,k8_relat_1(sK2,X10)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f35,f49])).

fof(f98,plain,
    ( spl6_8
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f91,f47,f37,f95])).

fof(f91,plain,
    ( k8_relat_1(sK2,sK2) = k8_relat_1(sK3,k8_relat_1(sK2,sK2))
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(resolution,[],[f67,f39])).

fof(f80,plain,
    ( spl6_7
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f69,f52,f42,f77])).

fof(f69,plain,
    ( k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3))
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(resolution,[],[f66,f44])).

fof(f66,plain,
    ( ! [X9] :
        ( ~ v1_relat_1(X9)
        | k8_relat_1(sK0,X9) = k8_relat_1(sK1,k8_relat_1(sK0,X9)) )
    | ~ spl6_4 ),
    inference(resolution,[],[f35,f54])).

fof(f75,plain,
    ( spl6_6
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f68,f52,f37,f72])).

fof(f68,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(resolution,[],[f66,f39])).

fof(f60,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

fof(f55,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f27,f52])).

fof(f27,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f26,f47])).

fof(f26,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f25,f42])).

fof(f25,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f24,f37])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:56:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.42  % (5339)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.42  % (5336)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  % (5338)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.44  % (5337)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.45  % (5341)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.46  % (5333)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.46  % (5342)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.46  % (5332)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.46  % (5340)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.47  % (5343)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.48  % (5334)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.48  % (5335)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.52  % (5340)Refutation not found, incomplete strategy% (5340)------------------------------
% 0.21/0.52  % (5340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5340)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5340)Memory used [KB]: 6012
% 0.21/0.52  % (5340)Time elapsed: 0.094 s
% 0.21/0.52  % (5340)------------------------------
% 0.21/0.52  % (5340)------------------------------
% 1.63/0.57  % (5341)Refutation found. Thanks to Tanya!
% 1.63/0.57  % SZS status Theorem for theBenchmark
% 1.63/0.57  % SZS output start Proof for theBenchmark
% 1.63/0.57  fof(f1140,plain,(
% 1.63/0.57    $false),
% 1.63/0.57    inference(avatar_sat_refutation,[],[f40,f45,f50,f55,f60,f75,f80,f98,f103,f122,f127,f143,f148,f308,f311,f313,f353,f369,f377,f380,f382,f440,f458,f461,f463,f522,f549,f552,f554,f614,f628,f652,f666,f684,f687,f689,f752,f777,f791,f817,f820,f822,f889,f1134,f1137,f1139])).
% 1.63/0.57  fof(f1139,plain,(
% 1.63/0.57    ~spl6_1 | spl6_40),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f1138])).
% 1.63/0.57  fof(f1138,plain,(
% 1.63/0.57    $false | (~spl6_1 | spl6_40)),
% 1.63/0.57    inference(subsumption_resolution,[],[f1136,f39])).
% 1.63/0.57  fof(f39,plain,(
% 1.63/0.57    v1_relat_1(sK2) | ~spl6_1),
% 1.63/0.57    inference(avatar_component_clause,[],[f37])).
% 1.63/0.57  fof(f37,plain,(
% 1.63/0.57    spl6_1 <=> v1_relat_1(sK2)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.63/0.57  fof(f1136,plain,(
% 1.63/0.57    ~v1_relat_1(sK2) | spl6_40),
% 1.63/0.57    inference(resolution,[],[f1133,f33])).
% 1.63/0.57  fof(f33,plain,(
% 1.63/0.57    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f12])).
% 1.63/0.57  fof(f12,plain,(
% 1.63/0.57    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 1.63/0.57    inference(ennf_transformation,[],[f3])).
% 1.63/0.57  fof(f3,axiom,(
% 1.63/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 1.63/0.57  fof(f1133,plain,(
% 1.63/0.57    ~r1_tarski(k8_relat_1(sK0,sK2),sK2) | spl6_40),
% 1.63/0.57    inference(avatar_component_clause,[],[f1131])).
% 1.63/0.57  fof(f1131,plain,(
% 1.63/0.57    spl6_40 <=> r1_tarski(k8_relat_1(sK0,sK2),sK2)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 1.63/0.57  fof(f1137,plain,(
% 1.63/0.57    ~spl6_1 | spl6_40),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f1135])).
% 1.63/0.57  fof(f1135,plain,(
% 1.63/0.57    $false | (~spl6_1 | spl6_40)),
% 1.63/0.57    inference(unit_resulting_resolution,[],[f39,f1133,f33])).
% 1.63/0.57  fof(f1134,plain,(
% 1.63/0.57    ~spl6_40 | ~spl6_1 | ~spl6_3 | ~spl6_14 | spl6_17),
% 1.63/0.57    inference(avatar_split_clause,[],[f1128,f366,f302,f47,f37,f1131])).
% 1.63/0.57  fof(f47,plain,(
% 1.63/0.57    spl6_3 <=> r1_tarski(sK2,sK3)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.63/0.57  fof(f302,plain,(
% 1.63/0.57    spl6_14 <=> v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.63/0.57  fof(f366,plain,(
% 1.63/0.57    spl6_17 <=> r1_tarski(k8_relat_1(sK0,sK2),sK3)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.63/0.57  fof(f1128,plain,(
% 1.63/0.57    ~r1_tarski(k8_relat_1(sK0,sK2),sK2) | (~spl6_1 | ~spl6_3 | ~spl6_14 | spl6_17)),
% 1.63/0.57    inference(subsumption_resolution,[],[f1122,f303])).
% 1.63/0.57  fof(f303,plain,(
% 1.63/0.57    v1_relat_1(k8_relat_1(sK0,sK2)) | ~spl6_14),
% 1.63/0.57    inference(avatar_component_clause,[],[f302])).
% 1.63/0.57  fof(f1122,plain,(
% 1.63/0.57    ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~r1_tarski(k8_relat_1(sK0,sK2),sK2) | (~spl6_1 | ~spl6_3 | spl6_17)),
% 1.63/0.57    inference(resolution,[],[f1120,f368])).
% 1.63/0.57  fof(f368,plain,(
% 1.63/0.57    ~r1_tarski(k8_relat_1(sK0,sK2),sK3) | spl6_17),
% 1.63/0.57    inference(avatar_component_clause,[],[f366])).
% 1.63/0.57  fof(f1120,plain,(
% 1.63/0.57    ( ! [X0] : (r1_tarski(X0,sK3) | ~v1_relat_1(X0) | ~r1_tarski(X0,sK2)) ) | (~spl6_1 | ~spl6_3)),
% 1.63/0.57    inference(duplicate_literal_removal,[],[f1118])).
% 1.63/0.57  fof(f1118,plain,(
% 1.63/0.57    ( ! [X0] : (r1_tarski(X0,sK3) | ~v1_relat_1(X0) | ~r1_tarski(X0,sK2) | r1_tarski(X0,sK3) | ~v1_relat_1(X0)) ) | (~spl6_1 | ~spl6_3)),
% 1.63/0.57    inference(resolution,[],[f1117,f31])).
% 1.63/0.57  fof(f31,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f23])).
% 1.63/0.57  fof(f23,plain,(
% 1.63/0.57    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.63/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f22])).
% 1.63/0.57  fof(f22,plain,(
% 1.63/0.57    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)))),
% 1.63/0.57    introduced(choice_axiom,[])).
% 1.63/0.57  fof(f21,plain,(
% 1.63/0.57    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.63/0.57    inference(rectify,[],[f20])).
% 1.63/0.57  fof(f20,plain,(
% 1.63/0.57    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.63/0.57    inference(nnf_transformation,[],[f10])).
% 1.63/0.57  fof(f10,plain,(
% 1.63/0.57    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 1.63/0.57    inference(ennf_transformation,[],[f1])).
% 1.63/0.57  fof(f1,axiom,(
% 1.63/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 1.63/0.57  fof(f1117,plain,(
% 1.63/0.57    ( ! [X62,X63] : (r2_hidden(k4_tarski(sK4(X62,X63),sK5(X62,X63)),sK3) | r1_tarski(X62,X63) | ~v1_relat_1(X62) | ~r1_tarski(X62,sK2)) ) | (~spl6_1 | ~spl6_3)),
% 1.63/0.57    inference(subsumption_resolution,[],[f1097,f39])).
% 1.63/0.57  fof(f1097,plain,(
% 1.63/0.57    ( ! [X62,X63] : (~v1_relat_1(X62) | r1_tarski(X62,X63) | r2_hidden(k4_tarski(sK4(X62,X63),sK5(X62,X63)),sK3) | ~r1_tarski(X62,sK2) | ~v1_relat_1(sK2)) ) | ~spl6_3),
% 1.63/0.57    inference(resolution,[],[f217,f49])).
% 1.63/0.57  fof(f49,plain,(
% 1.63/0.57    r1_tarski(sK2,sK3) | ~spl6_3),
% 1.63/0.57    inference(avatar_component_clause,[],[f47])).
% 1.63/0.57  fof(f217,plain,(
% 1.63/0.57    ( ! [X4,X2,X5,X3] : (~r1_tarski(X3,X5) | ~v1_relat_1(X2) | r1_tarski(X2,X4) | r2_hidden(k4_tarski(sK4(X2,X4),sK5(X2,X4)),X5) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) )),
% 1.63/0.57    inference(resolution,[],[f90,f29])).
% 1.63/0.57  fof(f29,plain,(
% 1.63/0.57    ( ! [X4,X0,X5,X1] : (~r2_hidden(k4_tarski(X4,X5),X0) | r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f23])).
% 1.63/0.57  fof(f90,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2) | ~r1_tarski(X0,X2) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) )),
% 1.63/0.57    inference(duplicate_literal_removal,[],[f89])).
% 1.63/0.57  fof(f89,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2) | ~r1_tarski(X0,X2) | ~v1_relat_1(X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.63/0.57    inference(resolution,[],[f29,f30])).
% 1.63/0.57  fof(f30,plain,(
% 1.63/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f23])).
% 1.63/0.57  fof(f889,plain,(
% 1.63/0.57    ~spl6_37 | spl6_39 | ~spl6_13),
% 1.63/0.57    inference(avatar_split_clause,[],[f154,f145,f887,f811])).
% 1.63/0.57  fof(f811,plain,(
% 1.63/0.57    spl6_37 <=> v1_relat_1(k8_relat_1(sK3,sK3))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 1.63/0.57  fof(f887,plain,(
% 1.63/0.57    spl6_39 <=> ! [X1] : (r1_tarski(k8_relat_1(sK3,sK3),k8_relat_1(sK3,X1)) | ~v1_relat_1(X1) | ~r1_tarski(k8_relat_1(sK3,sK3),X1))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 1.63/0.57  fof(f145,plain,(
% 1.63/0.57    spl6_13 <=> k8_relat_1(sK3,sK3) = k8_relat_1(sK3,k8_relat_1(sK3,sK3))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.63/0.57  fof(f154,plain,(
% 1.63/0.57    ( ! [X1] : (r1_tarski(k8_relat_1(sK3,sK3),k8_relat_1(sK3,X1)) | ~r1_tarski(k8_relat_1(sK3,sK3),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(sK3,sK3))) ) | ~spl6_13),
% 1.63/0.57    inference(superposition,[],[f34,f147])).
% 1.63/0.57  fof(f147,plain,(
% 1.63/0.57    k8_relat_1(sK3,sK3) = k8_relat_1(sK3,k8_relat_1(sK3,sK3)) | ~spl6_13),
% 1.63/0.57    inference(avatar_component_clause,[],[f145])).
% 1.63/0.57  fof(f34,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f14])).
% 1.63/0.57  fof(f14,plain,(
% 1.63/0.57    ! [X0,X1] : (! [X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.63/0.57    inference(flattening,[],[f13])).
% 1.63/0.57  fof(f13,plain,(
% 1.63/0.57    ! [X0,X1] : (! [X2] : ((r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.63/0.57    inference(ennf_transformation,[],[f5])).
% 1.63/0.57  fof(f5,axiom,(
% 1.63/0.57    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).
% 1.63/0.57  fof(f822,plain,(
% 1.63/0.57    ~spl6_2 | spl6_37),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f821])).
% 1.63/0.57  fof(f821,plain,(
% 1.63/0.57    $false | (~spl6_2 | spl6_37)),
% 1.63/0.57    inference(subsumption_resolution,[],[f819,f44])).
% 1.63/0.57  fof(f44,plain,(
% 1.63/0.57    v1_relat_1(sK3) | ~spl6_2),
% 1.63/0.57    inference(avatar_component_clause,[],[f42])).
% 1.63/0.57  fof(f42,plain,(
% 1.63/0.57    spl6_2 <=> v1_relat_1(sK3)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.63/0.57  fof(f819,plain,(
% 1.63/0.57    ~v1_relat_1(sK3) | spl6_37),
% 1.63/0.57    inference(resolution,[],[f813,f32])).
% 1.63/0.57  fof(f32,plain,(
% 1.63/0.57    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f11])).
% 1.63/0.57  fof(f11,plain,(
% 1.63/0.57    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 1.63/0.57    inference(ennf_transformation,[],[f2])).
% 1.63/0.57  fof(f2,axiom,(
% 1.63/0.57    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 1.63/0.57  fof(f813,plain,(
% 1.63/0.57    ~v1_relat_1(k8_relat_1(sK3,sK3)) | spl6_37),
% 1.63/0.57    inference(avatar_component_clause,[],[f811])).
% 1.63/0.57  fof(f820,plain,(
% 1.63/0.57    ~spl6_2 | spl6_37),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f818])).
% 1.63/0.57  fof(f818,plain,(
% 1.63/0.57    $false | (~spl6_2 | spl6_37)),
% 1.63/0.57    inference(unit_resulting_resolution,[],[f44,f813,f32])).
% 1.63/0.57  fof(f817,plain,(
% 1.63/0.57    ~spl6_37 | spl6_38 | ~spl6_13),
% 1.63/0.57    inference(avatar_split_clause,[],[f153,f145,f815,f811])).
% 1.63/0.57  fof(f815,plain,(
% 1.63/0.57    spl6_38 <=> ! [X0] : (r1_tarski(k8_relat_1(sK3,X0),k8_relat_1(sK3,sK3)) | ~v1_relat_1(X0) | ~r1_tarski(X0,k8_relat_1(sK3,sK3)))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 1.63/0.57  fof(f153,plain,(
% 1.63/0.57    ( ! [X0] : (r1_tarski(k8_relat_1(sK3,X0),k8_relat_1(sK3,sK3)) | ~r1_tarski(X0,k8_relat_1(sK3,sK3)) | ~v1_relat_1(k8_relat_1(sK3,sK3)) | ~v1_relat_1(X0)) ) | ~spl6_13),
% 1.63/0.57    inference(superposition,[],[f34,f147])).
% 1.63/0.57  fof(f791,plain,(
% 1.63/0.57    ~spl6_24 | spl6_36 | ~spl6_12),
% 1.63/0.57    inference(avatar_split_clause,[],[f150,f140,f789,f543])).
% 1.63/0.57  fof(f543,plain,(
% 1.63/0.57    spl6_24 <=> v1_relat_1(k8_relat_1(sK2,sK3))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.63/0.57  fof(f789,plain,(
% 1.63/0.57    spl6_36 <=> ! [X1] : (r1_tarski(k8_relat_1(sK2,sK3),k8_relat_1(sK2,X1)) | ~v1_relat_1(X1) | ~r1_tarski(k8_relat_1(sK2,sK3),X1))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 1.63/0.57  fof(f140,plain,(
% 1.63/0.57    spl6_12 <=> k8_relat_1(sK2,sK3) = k8_relat_1(sK2,k8_relat_1(sK2,sK3))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.63/0.57  fof(f150,plain,(
% 1.63/0.57    ( ! [X1] : (r1_tarski(k8_relat_1(sK2,sK3),k8_relat_1(sK2,X1)) | ~r1_tarski(k8_relat_1(sK2,sK3),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(sK2,sK3))) ) | ~spl6_12),
% 1.63/0.57    inference(superposition,[],[f34,f142])).
% 1.63/0.57  fof(f142,plain,(
% 1.63/0.57    k8_relat_1(sK2,sK3) = k8_relat_1(sK2,k8_relat_1(sK2,sK3)) | ~spl6_12),
% 1.63/0.57    inference(avatar_component_clause,[],[f140])).
% 1.63/0.57  fof(f777,plain,(
% 1.63/0.57    ~spl6_24 | spl6_35 | ~spl6_12),
% 1.63/0.57    inference(avatar_split_clause,[],[f149,f140,f775,f543])).
% 1.63/0.57  fof(f775,plain,(
% 1.63/0.57    spl6_35 <=> ! [X0] : (r1_tarski(k8_relat_1(sK2,X0),k8_relat_1(sK2,sK3)) | ~v1_relat_1(X0) | ~r1_tarski(X0,k8_relat_1(sK2,sK3)))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 1.63/0.57  fof(f149,plain,(
% 1.63/0.57    ( ! [X0] : (r1_tarski(k8_relat_1(sK2,X0),k8_relat_1(sK2,sK3)) | ~r1_tarski(X0,k8_relat_1(sK2,sK3)) | ~v1_relat_1(k8_relat_1(sK2,sK3)) | ~v1_relat_1(X0)) ) | ~spl6_12),
% 1.63/0.57    inference(superposition,[],[f34,f142])).
% 1.63/0.57  fof(f752,plain,(
% 1.63/0.57    ~spl6_32 | spl6_34 | ~spl6_11),
% 1.63/0.57    inference(avatar_split_clause,[],[f133,f124,f750,f678])).
% 1.63/0.57  fof(f678,plain,(
% 1.63/0.57    spl6_32 <=> v1_relat_1(k8_relat_1(sK3,sK2))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 1.63/0.57  fof(f750,plain,(
% 1.63/0.57    spl6_34 <=> ! [X1] : (r1_tarski(k8_relat_1(sK3,sK2),k8_relat_1(sK3,X1)) | ~v1_relat_1(X1) | ~r1_tarski(k8_relat_1(sK3,sK2),X1))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 1.63/0.57  fof(f124,plain,(
% 1.63/0.57    spl6_11 <=> k8_relat_1(sK3,sK2) = k8_relat_1(sK3,k8_relat_1(sK3,sK2))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.63/0.57  fof(f133,plain,(
% 1.63/0.57    ( ! [X1] : (r1_tarski(k8_relat_1(sK3,sK2),k8_relat_1(sK3,X1)) | ~r1_tarski(k8_relat_1(sK3,sK2),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(sK3,sK2))) ) | ~spl6_11),
% 1.63/0.57    inference(superposition,[],[f34,f126])).
% 1.63/0.57  fof(f126,plain,(
% 1.63/0.57    k8_relat_1(sK3,sK2) = k8_relat_1(sK3,k8_relat_1(sK3,sK2)) | ~spl6_11),
% 1.63/0.57    inference(avatar_component_clause,[],[f124])).
% 1.63/0.57  fof(f689,plain,(
% 1.63/0.57    ~spl6_1 | spl6_32),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f688])).
% 1.63/0.57  fof(f688,plain,(
% 1.63/0.57    $false | (~spl6_1 | spl6_32)),
% 1.63/0.57    inference(subsumption_resolution,[],[f686,f39])).
% 1.63/0.57  fof(f686,plain,(
% 1.63/0.57    ~v1_relat_1(sK2) | spl6_32),
% 1.63/0.57    inference(resolution,[],[f680,f32])).
% 1.63/0.57  fof(f680,plain,(
% 1.63/0.57    ~v1_relat_1(k8_relat_1(sK3,sK2)) | spl6_32),
% 1.63/0.57    inference(avatar_component_clause,[],[f678])).
% 1.63/0.57  fof(f687,plain,(
% 1.63/0.57    ~spl6_1 | spl6_32),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f685])).
% 1.63/0.57  fof(f685,plain,(
% 1.63/0.57    $false | (~spl6_1 | spl6_32)),
% 1.63/0.57    inference(unit_resulting_resolution,[],[f39,f680,f32])).
% 1.63/0.57  fof(f684,plain,(
% 1.63/0.57    ~spl6_32 | spl6_33 | ~spl6_11),
% 1.63/0.57    inference(avatar_split_clause,[],[f132,f124,f682,f678])).
% 1.63/0.57  fof(f682,plain,(
% 1.63/0.57    spl6_33 <=> ! [X0] : (r1_tarski(k8_relat_1(sK3,X0),k8_relat_1(sK3,sK2)) | ~v1_relat_1(X0) | ~r1_tarski(X0,k8_relat_1(sK3,sK2)))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 1.63/0.57  fof(f132,plain,(
% 1.63/0.57    ( ! [X0] : (r1_tarski(k8_relat_1(sK3,X0),k8_relat_1(sK3,sK2)) | ~r1_tarski(X0,k8_relat_1(sK3,sK2)) | ~v1_relat_1(k8_relat_1(sK3,sK2)) | ~v1_relat_1(X0)) ) | ~spl6_11),
% 1.63/0.57    inference(superposition,[],[f34,f126])).
% 1.63/0.57  fof(f666,plain,(
% 1.63/0.57    ~spl6_21 | spl6_31 | ~spl6_10),
% 1.63/0.57    inference(avatar_split_clause,[],[f129,f119,f664,f452])).
% 1.63/0.57  fof(f452,plain,(
% 1.63/0.57    spl6_21 <=> v1_relat_1(k8_relat_1(sK2,sK2))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.63/0.57  fof(f664,plain,(
% 1.63/0.57    spl6_31 <=> ! [X1] : (r1_tarski(k8_relat_1(sK2,sK2),k8_relat_1(sK2,X1)) | ~v1_relat_1(X1) | ~r1_tarski(k8_relat_1(sK2,sK2),X1))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 1.63/0.57  fof(f119,plain,(
% 1.63/0.57    spl6_10 <=> k8_relat_1(sK2,sK2) = k8_relat_1(sK2,k8_relat_1(sK2,sK2))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.63/0.57  fof(f129,plain,(
% 1.63/0.57    ( ! [X1] : (r1_tarski(k8_relat_1(sK2,sK2),k8_relat_1(sK2,X1)) | ~r1_tarski(k8_relat_1(sK2,sK2),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(sK2,sK2))) ) | ~spl6_10),
% 1.63/0.57    inference(superposition,[],[f34,f121])).
% 1.63/0.57  fof(f121,plain,(
% 1.63/0.57    k8_relat_1(sK2,sK2) = k8_relat_1(sK2,k8_relat_1(sK2,sK2)) | ~spl6_10),
% 1.63/0.57    inference(avatar_component_clause,[],[f119])).
% 1.63/0.57  fof(f652,plain,(
% 1.63/0.57    ~spl6_21 | spl6_30 | ~spl6_10),
% 1.63/0.57    inference(avatar_split_clause,[],[f128,f119,f650,f452])).
% 1.63/0.57  fof(f650,plain,(
% 1.63/0.57    spl6_30 <=> ! [X0] : (r1_tarski(k8_relat_1(sK2,X0),k8_relat_1(sK2,sK2)) | ~v1_relat_1(X0) | ~r1_tarski(X0,k8_relat_1(sK2,sK2)))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 1.63/0.57  fof(f128,plain,(
% 1.63/0.57    ( ! [X0] : (r1_tarski(k8_relat_1(sK2,X0),k8_relat_1(sK2,sK2)) | ~r1_tarski(X0,k8_relat_1(sK2,sK2)) | ~v1_relat_1(k8_relat_1(sK2,sK2)) | ~v1_relat_1(X0)) ) | ~spl6_10),
% 1.63/0.57    inference(superposition,[],[f34,f121])).
% 1.63/0.57  fof(f628,plain,(
% 1.63/0.57    ~spl6_24 | spl6_29 | ~spl6_9),
% 1.63/0.57    inference(avatar_split_clause,[],[f109,f100,f626,f543])).
% 1.63/0.57  fof(f626,plain,(
% 1.63/0.57    spl6_29 <=> ! [X1] : (r1_tarski(k8_relat_1(sK2,sK3),k8_relat_1(sK3,X1)) | ~v1_relat_1(X1) | ~r1_tarski(k8_relat_1(sK2,sK3),X1))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 1.63/0.57  fof(f100,plain,(
% 1.63/0.57    spl6_9 <=> k8_relat_1(sK2,sK3) = k8_relat_1(sK3,k8_relat_1(sK2,sK3))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.63/0.57  fof(f109,plain,(
% 1.63/0.57    ( ! [X1] : (r1_tarski(k8_relat_1(sK2,sK3),k8_relat_1(sK3,X1)) | ~r1_tarski(k8_relat_1(sK2,sK3),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(sK2,sK3))) ) | ~spl6_9),
% 1.63/0.57    inference(superposition,[],[f34,f102])).
% 1.63/0.57  fof(f102,plain,(
% 1.63/0.57    k8_relat_1(sK2,sK3) = k8_relat_1(sK3,k8_relat_1(sK2,sK3)) | ~spl6_9),
% 1.63/0.57    inference(avatar_component_clause,[],[f100])).
% 1.63/0.57  fof(f614,plain,(
% 1.63/0.57    ~spl6_26 | ~spl6_27 | spl6_28 | ~spl6_4),
% 1.63/0.57    inference(avatar_split_clause,[],[f266,f52,f612,f608,f604])).
% 1.63/0.57  fof(f604,plain,(
% 1.63/0.57    spl6_26 <=> v1_relat_1(sK0)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.63/0.57  fof(f608,plain,(
% 1.63/0.57    spl6_27 <=> v1_relat_1(sK1)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.63/0.57  fof(f612,plain,(
% 1.63/0.57    spl6_28 <=> ! [X13,X12] : (~v1_relat_1(X12) | k8_relat_1(k8_relat_1(X13,sK0),X12) = k8_relat_1(k8_relat_1(X13,sK1),k8_relat_1(k8_relat_1(X13,sK0),X12)))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 1.63/0.57  fof(f52,plain,(
% 1.63/0.57    spl6_4 <=> r1_tarski(sK0,sK1)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.63/0.57  fof(f266,plain,(
% 1.63/0.57    ( ! [X12,X13] : (~v1_relat_1(X12) | k8_relat_1(k8_relat_1(X13,sK0),X12) = k8_relat_1(k8_relat_1(X13,sK1),k8_relat_1(k8_relat_1(X13,sK0),X12)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)) ) | ~spl6_4),
% 1.63/0.57    inference(resolution,[],[f65,f54])).
% 1.63/0.57  fof(f54,plain,(
% 1.63/0.57    r1_tarski(sK0,sK1) | ~spl6_4),
% 1.63/0.57    inference(avatar_component_clause,[],[f52])).
% 1.63/0.57  fof(f65,plain,(
% 1.63/0.57    ( ! [X6,X8,X7,X5] : (~r1_tarski(X6,X8) | ~v1_relat_1(X7) | k8_relat_1(k8_relat_1(X5,X6),X7) = k8_relat_1(k8_relat_1(X5,X8),k8_relat_1(k8_relat_1(X5,X6),X7)) | ~v1_relat_1(X8) | ~v1_relat_1(X6)) )),
% 1.63/0.57    inference(resolution,[],[f35,f34])).
% 1.63/0.57  fof(f35,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f16])).
% 1.63/0.57  fof(f16,plain,(
% 1.63/0.57    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.63/0.57    inference(flattening,[],[f15])).
% 1.63/0.57  fof(f15,plain,(
% 1.63/0.57    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.63/0.57    inference(ennf_transformation,[],[f4])).
% 1.63/0.57  fof(f4,axiom,(
% 1.63/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).
% 1.63/0.57  fof(f554,plain,(
% 1.63/0.57    ~spl6_2 | spl6_24),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f553])).
% 1.63/0.57  fof(f553,plain,(
% 1.63/0.57    $false | (~spl6_2 | spl6_24)),
% 1.63/0.57    inference(subsumption_resolution,[],[f551,f44])).
% 1.63/0.57  fof(f551,plain,(
% 1.63/0.57    ~v1_relat_1(sK3) | spl6_24),
% 1.63/0.57    inference(resolution,[],[f545,f32])).
% 1.63/0.57  fof(f545,plain,(
% 1.63/0.57    ~v1_relat_1(k8_relat_1(sK2,sK3)) | spl6_24),
% 1.63/0.57    inference(avatar_component_clause,[],[f543])).
% 1.63/0.57  fof(f552,plain,(
% 1.63/0.57    ~spl6_2 | spl6_24),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f550])).
% 1.63/0.57  fof(f550,plain,(
% 1.63/0.57    $false | (~spl6_2 | spl6_24)),
% 1.63/0.57    inference(unit_resulting_resolution,[],[f44,f545,f32])).
% 1.63/0.57  fof(f549,plain,(
% 1.63/0.57    ~spl6_24 | spl6_25 | ~spl6_9),
% 1.63/0.57    inference(avatar_split_clause,[],[f108,f100,f547,f543])).
% 1.63/0.57  fof(f547,plain,(
% 1.63/0.57    spl6_25 <=> ! [X0] : (r1_tarski(k8_relat_1(sK3,X0),k8_relat_1(sK2,sK3)) | ~v1_relat_1(X0) | ~r1_tarski(X0,k8_relat_1(sK2,sK3)))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.63/0.57  fof(f108,plain,(
% 1.63/0.57    ( ! [X0] : (r1_tarski(k8_relat_1(sK3,X0),k8_relat_1(sK2,sK3)) | ~r1_tarski(X0,k8_relat_1(sK2,sK3)) | ~v1_relat_1(k8_relat_1(sK2,sK3)) | ~v1_relat_1(X0)) ) | ~spl6_9),
% 1.63/0.57    inference(superposition,[],[f34,f102])).
% 1.63/0.57  fof(f522,plain,(
% 1.63/0.57    ~spl6_21 | spl6_23 | ~spl6_8),
% 1.63/0.57    inference(avatar_split_clause,[],[f105,f95,f520,f452])).
% 1.63/0.57  fof(f520,plain,(
% 1.63/0.57    spl6_23 <=> ! [X1] : (r1_tarski(k8_relat_1(sK2,sK2),k8_relat_1(sK3,X1)) | ~v1_relat_1(X1) | ~r1_tarski(k8_relat_1(sK2,sK2),X1))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.63/0.57  fof(f95,plain,(
% 1.63/0.57    spl6_8 <=> k8_relat_1(sK2,sK2) = k8_relat_1(sK3,k8_relat_1(sK2,sK2))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.63/0.57  fof(f105,plain,(
% 1.63/0.57    ( ! [X1] : (r1_tarski(k8_relat_1(sK2,sK2),k8_relat_1(sK3,X1)) | ~r1_tarski(k8_relat_1(sK2,sK2),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(sK2,sK2))) ) | ~spl6_8),
% 1.63/0.57    inference(superposition,[],[f34,f97])).
% 1.63/0.57  fof(f97,plain,(
% 1.63/0.57    k8_relat_1(sK2,sK2) = k8_relat_1(sK3,k8_relat_1(sK2,sK2)) | ~spl6_8),
% 1.63/0.57    inference(avatar_component_clause,[],[f95])).
% 1.63/0.57  fof(f463,plain,(
% 1.63/0.57    ~spl6_1 | spl6_21),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f462])).
% 1.63/0.57  fof(f462,plain,(
% 1.63/0.57    $false | (~spl6_1 | spl6_21)),
% 1.63/0.57    inference(subsumption_resolution,[],[f460,f39])).
% 1.63/0.57  fof(f460,plain,(
% 1.63/0.57    ~v1_relat_1(sK2) | spl6_21),
% 1.63/0.57    inference(resolution,[],[f454,f32])).
% 1.63/0.57  fof(f454,plain,(
% 1.63/0.57    ~v1_relat_1(k8_relat_1(sK2,sK2)) | spl6_21),
% 1.63/0.57    inference(avatar_component_clause,[],[f452])).
% 1.63/0.57  fof(f461,plain,(
% 1.63/0.57    ~spl6_1 | spl6_21),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f459])).
% 1.63/0.57  fof(f459,plain,(
% 1.63/0.57    $false | (~spl6_1 | spl6_21)),
% 1.63/0.57    inference(unit_resulting_resolution,[],[f39,f454,f32])).
% 1.63/0.57  fof(f458,plain,(
% 1.63/0.57    ~spl6_21 | spl6_22 | ~spl6_8),
% 1.63/0.57    inference(avatar_split_clause,[],[f104,f95,f456,f452])).
% 1.63/0.57  fof(f456,plain,(
% 1.63/0.57    spl6_22 <=> ! [X0] : (r1_tarski(k8_relat_1(sK3,X0),k8_relat_1(sK2,sK2)) | ~v1_relat_1(X0) | ~r1_tarski(X0,k8_relat_1(sK2,sK2)))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.63/0.57  fof(f104,plain,(
% 1.63/0.57    ( ! [X0] : (r1_tarski(k8_relat_1(sK3,X0),k8_relat_1(sK2,sK2)) | ~r1_tarski(X0,k8_relat_1(sK2,sK2)) | ~v1_relat_1(k8_relat_1(sK2,sK2)) | ~v1_relat_1(X0)) ) | ~spl6_8),
% 1.63/0.57    inference(superposition,[],[f34,f97])).
% 1.63/0.57  fof(f440,plain,(
% 1.63/0.57    ~spl6_18 | spl6_20 | ~spl6_7),
% 1.63/0.57    inference(avatar_split_clause,[],[f86,f77,f438,f371])).
% 1.63/0.57  fof(f371,plain,(
% 1.63/0.57    spl6_18 <=> v1_relat_1(k8_relat_1(sK0,sK3))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.63/0.57  fof(f438,plain,(
% 1.63/0.57    spl6_20 <=> ! [X1] : (r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,X1)) | ~v1_relat_1(X1) | ~r1_tarski(k8_relat_1(sK0,sK3),X1))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.63/0.57  fof(f77,plain,(
% 1.63/0.57    spl6_7 <=> k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.63/0.57  fof(f86,plain,(
% 1.63/0.57    ( ! [X1] : (r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,X1)) | ~r1_tarski(k8_relat_1(sK0,sK3),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(sK0,sK3))) ) | ~spl6_7),
% 1.63/0.57    inference(superposition,[],[f34,f79])).
% 1.63/0.57  fof(f79,plain,(
% 1.63/0.57    k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3)) | ~spl6_7),
% 1.63/0.57    inference(avatar_component_clause,[],[f77])).
% 1.63/0.57  fof(f382,plain,(
% 1.63/0.57    ~spl6_2 | spl6_18),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f381])).
% 1.63/0.57  fof(f381,plain,(
% 1.63/0.57    $false | (~spl6_2 | spl6_18)),
% 1.63/0.57    inference(subsumption_resolution,[],[f379,f44])).
% 1.63/0.57  fof(f379,plain,(
% 1.63/0.57    ~v1_relat_1(sK3) | spl6_18),
% 1.63/0.57    inference(resolution,[],[f373,f32])).
% 1.63/0.57  fof(f373,plain,(
% 1.63/0.57    ~v1_relat_1(k8_relat_1(sK0,sK3)) | spl6_18),
% 1.63/0.57    inference(avatar_component_clause,[],[f371])).
% 1.63/0.57  fof(f380,plain,(
% 1.63/0.57    ~spl6_2 | spl6_18),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f378])).
% 1.63/0.57  fof(f378,plain,(
% 1.63/0.57    $false | (~spl6_2 | spl6_18)),
% 1.63/0.57    inference(unit_resulting_resolution,[],[f44,f373,f32])).
% 1.63/0.57  fof(f377,plain,(
% 1.63/0.57    ~spl6_18 | spl6_19 | ~spl6_7),
% 1.63/0.57    inference(avatar_split_clause,[],[f85,f77,f375,f371])).
% 1.63/0.57  fof(f375,plain,(
% 1.63/0.57    spl6_19 <=> ! [X0] : (r1_tarski(k8_relat_1(sK1,X0),k8_relat_1(sK0,sK3)) | ~v1_relat_1(X0) | ~r1_tarski(X0,k8_relat_1(sK0,sK3)))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.63/0.57  fof(f85,plain,(
% 1.63/0.57    ( ! [X0] : (r1_tarski(k8_relat_1(sK1,X0),k8_relat_1(sK0,sK3)) | ~r1_tarski(X0,k8_relat_1(sK0,sK3)) | ~v1_relat_1(k8_relat_1(sK0,sK3)) | ~v1_relat_1(X0)) ) | ~spl6_7),
% 1.63/0.57    inference(superposition,[],[f34,f79])).
% 1.63/0.57  fof(f369,plain,(
% 1.63/0.57    ~spl6_17 | ~spl6_2 | spl6_5 | ~spl6_16),
% 1.63/0.57    inference(avatar_split_clause,[],[f362,f351,f57,f42,f366])).
% 1.63/0.57  fof(f57,plain,(
% 1.63/0.57    spl6_5 <=> r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.63/0.57  fof(f351,plain,(
% 1.63/0.57    spl6_16 <=> ! [X1] : (r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X1)) | ~v1_relat_1(X1) | ~r1_tarski(k8_relat_1(sK0,sK2),X1))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.63/0.57  fof(f362,plain,(
% 1.63/0.57    ~r1_tarski(k8_relat_1(sK0,sK2),sK3) | (~spl6_2 | spl6_5 | ~spl6_16)),
% 1.63/0.57    inference(subsumption_resolution,[],[f354,f44])).
% 1.63/0.57  fof(f354,plain,(
% 1.63/0.57    ~v1_relat_1(sK3) | ~r1_tarski(k8_relat_1(sK0,sK2),sK3) | (spl6_5 | ~spl6_16)),
% 1.63/0.57    inference(resolution,[],[f352,f59])).
% 1.63/0.57  fof(f59,plain,(
% 1.63/0.57    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) | spl6_5),
% 1.63/0.57    inference(avatar_component_clause,[],[f57])).
% 1.63/0.57  fof(f352,plain,(
% 1.63/0.57    ( ! [X1] : (r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X1)) | ~v1_relat_1(X1) | ~r1_tarski(k8_relat_1(sK0,sK2),X1)) ) | ~spl6_16),
% 1.63/0.57    inference(avatar_component_clause,[],[f351])).
% 1.63/0.57  fof(f353,plain,(
% 1.63/0.57    ~spl6_14 | spl6_16 | ~spl6_6),
% 1.63/0.57    inference(avatar_split_clause,[],[f82,f72,f351,f302])).
% 1.63/0.57  fof(f72,plain,(
% 1.63/0.57    spl6_6 <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.63/0.57  fof(f82,plain,(
% 1.63/0.57    ( ! [X1] : (r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X1)) | ~r1_tarski(k8_relat_1(sK0,sK2),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(sK0,sK2))) ) | ~spl6_6),
% 1.63/0.57    inference(superposition,[],[f34,f74])).
% 1.63/0.57  fof(f74,plain,(
% 1.63/0.57    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | ~spl6_6),
% 1.63/0.57    inference(avatar_component_clause,[],[f72])).
% 1.63/0.57  fof(f313,plain,(
% 1.63/0.57    ~spl6_1 | spl6_14),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f312])).
% 1.63/0.57  fof(f312,plain,(
% 1.63/0.57    $false | (~spl6_1 | spl6_14)),
% 1.63/0.57    inference(subsumption_resolution,[],[f310,f39])).
% 1.63/0.57  fof(f310,plain,(
% 1.63/0.57    ~v1_relat_1(sK2) | spl6_14),
% 1.63/0.57    inference(resolution,[],[f304,f32])).
% 1.63/0.57  fof(f304,plain,(
% 1.63/0.57    ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl6_14),
% 1.63/0.57    inference(avatar_component_clause,[],[f302])).
% 1.63/0.57  fof(f311,plain,(
% 1.63/0.57    ~spl6_1 | spl6_14),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f309])).
% 1.63/0.57  fof(f309,plain,(
% 1.63/0.57    $false | (~spl6_1 | spl6_14)),
% 1.63/0.57    inference(unit_resulting_resolution,[],[f39,f304,f32])).
% 1.63/0.57  fof(f308,plain,(
% 1.63/0.57    ~spl6_14 | spl6_15 | ~spl6_6),
% 1.63/0.57    inference(avatar_split_clause,[],[f81,f72,f306,f302])).
% 1.63/0.57  fof(f306,plain,(
% 1.63/0.57    spl6_15 <=> ! [X0] : (r1_tarski(k8_relat_1(sK1,X0),k8_relat_1(sK0,sK2)) | ~v1_relat_1(X0) | ~r1_tarski(X0,k8_relat_1(sK0,sK2)))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.63/0.57  fof(f81,plain,(
% 1.63/0.57    ( ! [X0] : (r1_tarski(k8_relat_1(sK1,X0),k8_relat_1(sK0,sK2)) | ~r1_tarski(X0,k8_relat_1(sK0,sK2)) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(X0)) ) | ~spl6_6),
% 1.63/0.57    inference(superposition,[],[f34,f74])).
% 1.63/0.57  fof(f148,plain,(
% 1.63/0.57    spl6_13 | ~spl6_2),
% 1.63/0.57    inference(avatar_split_clause,[],[f137,f42,f145])).
% 1.63/0.57  fof(f137,plain,(
% 1.63/0.57    k8_relat_1(sK3,sK3) = k8_relat_1(sK3,k8_relat_1(sK3,sK3)) | ~spl6_2),
% 1.63/0.57    inference(resolution,[],[f113,f44])).
% 1.63/0.57  fof(f113,plain,(
% 1.63/0.57    ( ! [X1] : (~v1_relat_1(X1) | k8_relat_1(X1,sK3) = k8_relat_1(X1,k8_relat_1(X1,sK3))) ) | ~spl6_2),
% 1.63/0.57    inference(resolution,[],[f63,f44])).
% 1.63/0.57  fof(f63,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.63/0.57    inference(resolution,[],[f35,f62])).
% 1.63/0.57  fof(f62,plain,(
% 1.63/0.57    ( ! [X0] : (r1_tarski(X0,X0) | ~v1_relat_1(X0)) )),
% 1.63/0.57    inference(duplicate_literal_removal,[],[f61])).
% 1.63/0.57  fof(f61,plain,(
% 1.63/0.57    ( ! [X0] : (r1_tarski(X0,X0) | ~v1_relat_1(X0) | r1_tarski(X0,X0) | ~v1_relat_1(X0)) )),
% 1.63/0.57    inference(resolution,[],[f31,f30])).
% 1.63/0.57  fof(f143,plain,(
% 1.63/0.57    spl6_12 | ~spl6_1 | ~spl6_2),
% 1.63/0.57    inference(avatar_split_clause,[],[f136,f42,f37,f140])).
% 1.63/0.57  fof(f136,plain,(
% 1.63/0.57    k8_relat_1(sK2,sK3) = k8_relat_1(sK2,k8_relat_1(sK2,sK3)) | (~spl6_1 | ~spl6_2)),
% 1.63/0.57    inference(resolution,[],[f113,f39])).
% 1.63/0.57  fof(f127,plain,(
% 1.63/0.57    spl6_11 | ~spl6_1 | ~spl6_2),
% 1.63/0.57    inference(avatar_split_clause,[],[f116,f42,f37,f124])).
% 1.63/0.57  fof(f116,plain,(
% 1.63/0.57    k8_relat_1(sK3,sK2) = k8_relat_1(sK3,k8_relat_1(sK3,sK2)) | (~spl6_1 | ~spl6_2)),
% 1.63/0.57    inference(resolution,[],[f112,f44])).
% 1.63/0.57  fof(f112,plain,(
% 1.63/0.57    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X0,sK2))) ) | ~spl6_1),
% 1.63/0.57    inference(resolution,[],[f63,f39])).
% 1.63/0.57  fof(f122,plain,(
% 1.63/0.57    spl6_10 | ~spl6_1),
% 1.63/0.57    inference(avatar_split_clause,[],[f115,f37,f119])).
% 1.63/0.57  fof(f115,plain,(
% 1.63/0.57    k8_relat_1(sK2,sK2) = k8_relat_1(sK2,k8_relat_1(sK2,sK2)) | ~spl6_1),
% 1.63/0.57    inference(resolution,[],[f112,f39])).
% 1.63/0.57  fof(f103,plain,(
% 1.63/0.57    spl6_9 | ~spl6_2 | ~spl6_3),
% 1.63/0.57    inference(avatar_split_clause,[],[f92,f47,f42,f100])).
% 1.63/0.57  fof(f92,plain,(
% 1.63/0.57    k8_relat_1(sK2,sK3) = k8_relat_1(sK3,k8_relat_1(sK2,sK3)) | (~spl6_2 | ~spl6_3)),
% 1.63/0.57    inference(resolution,[],[f67,f44])).
% 1.63/0.57  fof(f67,plain,(
% 1.63/0.57    ( ! [X10] : (~v1_relat_1(X10) | k8_relat_1(sK2,X10) = k8_relat_1(sK3,k8_relat_1(sK2,X10))) ) | ~spl6_3),
% 1.63/0.57    inference(resolution,[],[f35,f49])).
% 1.63/0.57  fof(f98,plain,(
% 1.63/0.57    spl6_8 | ~spl6_1 | ~spl6_3),
% 1.63/0.57    inference(avatar_split_clause,[],[f91,f47,f37,f95])).
% 1.63/0.57  fof(f91,plain,(
% 1.63/0.57    k8_relat_1(sK2,sK2) = k8_relat_1(sK3,k8_relat_1(sK2,sK2)) | (~spl6_1 | ~spl6_3)),
% 1.63/0.57    inference(resolution,[],[f67,f39])).
% 1.63/0.57  fof(f80,plain,(
% 1.63/0.57    spl6_7 | ~spl6_2 | ~spl6_4),
% 1.63/0.57    inference(avatar_split_clause,[],[f69,f52,f42,f77])).
% 1.63/0.57  fof(f69,plain,(
% 1.63/0.57    k8_relat_1(sK0,sK3) = k8_relat_1(sK1,k8_relat_1(sK0,sK3)) | (~spl6_2 | ~spl6_4)),
% 1.63/0.57    inference(resolution,[],[f66,f44])).
% 1.63/0.57  fof(f66,plain,(
% 1.63/0.57    ( ! [X9] : (~v1_relat_1(X9) | k8_relat_1(sK0,X9) = k8_relat_1(sK1,k8_relat_1(sK0,X9))) ) | ~spl6_4),
% 1.63/0.57    inference(resolution,[],[f35,f54])).
% 1.63/0.57  fof(f75,plain,(
% 1.63/0.57    spl6_6 | ~spl6_1 | ~spl6_4),
% 1.63/0.57    inference(avatar_split_clause,[],[f68,f52,f37,f72])).
% 1.63/0.57  fof(f68,plain,(
% 1.63/0.57    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | (~spl6_1 | ~spl6_4)),
% 1.63/0.57    inference(resolution,[],[f66,f39])).
% 1.63/0.57  fof(f60,plain,(
% 1.63/0.57    ~spl6_5),
% 1.63/0.57    inference(avatar_split_clause,[],[f28,f57])).
% 1.63/0.57  fof(f28,plain,(
% 1.63/0.57    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 1.63/0.57    inference(cnf_transformation,[],[f19])).
% 1.63/0.57  fof(f19,plain,(
% 1.63/0.57    (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 1.63/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f18,f17])).
% 1.63/0.57  fof(f17,plain,(
% 1.63/0.57    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 1.63/0.57    introduced(choice_axiom,[])).
% 1.63/0.57  fof(f18,plain,(
% 1.63/0.57    ? [X3] : (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 1.63/0.57    introduced(choice_axiom,[])).
% 1.63/0.57  fof(f9,plain,(
% 1.63/0.57    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 1.63/0.57    inference(flattening,[],[f8])).
% 1.63/0.57  fof(f8,plain,(
% 1.63/0.57    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 1.63/0.57    inference(ennf_transformation,[],[f7])).
% 1.63/0.57  fof(f7,negated_conjecture,(
% 1.63/0.57    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 1.63/0.57    inference(negated_conjecture,[],[f6])).
% 1.63/0.57  fof(f6,conjecture,(
% 1.63/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 1.63/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).
% 1.63/0.57  fof(f55,plain,(
% 1.63/0.57    spl6_4),
% 1.63/0.57    inference(avatar_split_clause,[],[f27,f52])).
% 1.63/0.57  fof(f27,plain,(
% 1.63/0.57    r1_tarski(sK0,sK1)),
% 1.63/0.57    inference(cnf_transformation,[],[f19])).
% 1.63/0.57  fof(f50,plain,(
% 1.63/0.57    spl6_3),
% 1.63/0.57    inference(avatar_split_clause,[],[f26,f47])).
% 1.63/0.57  fof(f26,plain,(
% 1.63/0.57    r1_tarski(sK2,sK3)),
% 1.63/0.57    inference(cnf_transformation,[],[f19])).
% 1.63/0.57  fof(f45,plain,(
% 1.63/0.57    spl6_2),
% 1.63/0.57    inference(avatar_split_clause,[],[f25,f42])).
% 1.63/0.57  fof(f25,plain,(
% 1.63/0.57    v1_relat_1(sK3)),
% 1.63/0.57    inference(cnf_transformation,[],[f19])).
% 1.63/0.57  fof(f40,plain,(
% 1.63/0.57    spl6_1),
% 1.63/0.57    inference(avatar_split_clause,[],[f24,f37])).
% 1.63/0.57  fof(f24,plain,(
% 1.63/0.57    v1_relat_1(sK2)),
% 1.63/0.57    inference(cnf_transformation,[],[f19])).
% 1.63/0.57  % SZS output end Proof for theBenchmark
% 1.63/0.57  % (5341)------------------------------
% 1.63/0.57  % (5341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (5341)Termination reason: Refutation
% 1.63/0.57  
% 1.63/0.57  % (5341)Memory used [KB]: 2814
% 1.63/0.57  % (5341)Time elapsed: 0.148 s
% 1.63/0.57  % (5341)------------------------------
% 1.63/0.57  % (5341)------------------------------
% 1.63/0.57  % (5331)Success in time 0.207 s
%------------------------------------------------------------------------------

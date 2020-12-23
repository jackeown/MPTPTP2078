%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0461+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:01 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 212 expanded)
%              Number of leaves         :    9 (  50 expanded)
%              Depth                    :   25
%              Number of atoms          :  305 ( 903 expanded)
%              Number of equality atoms :    5 (  18 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f381,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f54,f370,f375])).

fof(f375,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_5 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_5 ),
    inference(subsumption_resolution,[],[f373,f38])).

fof(f38,plain,
    ( v1_relat_1(sK1)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl9_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f373,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | spl9_5 ),
    inference(subsumption_resolution,[],[f372,f48])).

fof(f48,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl9_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f372,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_5 ),
    inference(subsumption_resolution,[],[f371,f33])).

fof(f33,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl9_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f371,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_3
    | spl9_5 ),
    inference(subsumption_resolution,[],[f363,f43])).

fof(f43,plain,
    ( v1_relat_1(sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl9_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f363,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | spl9_5 ),
    inference(resolution,[],[f361,f53])).

fof(f53,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))
    | spl9_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl9_5
  <=> r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f361,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X0,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f360,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f360,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X0)
      | r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X0,X2))
      | ~ v1_relat_1(k5_relat_1(X0,X2)) ) ),
    inference(resolution,[],[f341,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f25,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f341,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X3,X0)
      | r1_tarski(k5_relat_1(X3,X1),X2) ) ),
    inference(subsumption_resolution,[],[f340,f26])).

fof(f340,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X3,X0)
      | r1_tarski(k5_relat_1(X3,X1),X2)
      | ~ v1_relat_1(k5_relat_1(X3,X1)) ) ),
    inference(duplicate_literal_removal,[],[f332])).

fof(f332,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X3,X0)
      | r1_tarski(k5_relat_1(X3,X1),X2)
      | ~ v1_relat_1(k5_relat_1(X3,X1))
      | r1_tarski(k5_relat_1(X3,X1),X2) ) ),
    inference(resolution,[],[f213,f25])).

fof(f213,plain,(
    ! [X80,X83,X81,X79,X82] :
      ( r2_hidden(k4_tarski(sK7(k5_relat_1(X80,X81),X82),sK8(k5_relat_1(X80,X81),X82)),X83)
      | ~ v1_relat_1(X79)
      | ~ r1_tarski(k5_relat_1(X79,X81),X83)
      | ~ v1_relat_1(X80)
      | ~ v1_relat_1(X81)
      | ~ r1_tarski(X80,X79)
      | r1_tarski(k5_relat_1(X80,X81),X82) ) ),
    inference(subsumption_resolution,[],[f200,f26])).

fof(f200,plain,(
    ! [X80,X83,X81,X79,X82] :
      ( ~ v1_relat_1(X79)
      | r2_hidden(k4_tarski(sK7(k5_relat_1(X80,X81),X82),sK8(k5_relat_1(X80,X81),X82)),X83)
      | ~ r1_tarski(k5_relat_1(X79,X81),X83)
      | ~ v1_relat_1(X80)
      | ~ v1_relat_1(X81)
      | ~ r1_tarski(X80,X79)
      | ~ v1_relat_1(k5_relat_1(X80,X81))
      | r1_tarski(k5_relat_1(X80,X81),X82) ) ),
    inference(resolution,[],[f184,f24])).

fof(f184,plain,(
    ! [X14,X12,X17,X15,X13,X16] :
      ( ~ r2_hidden(k4_tarski(X14,X15),k5_relat_1(X17,X12))
      | ~ v1_relat_1(X13)
      | r2_hidden(k4_tarski(X14,X15),X16)
      | ~ r1_tarski(k5_relat_1(X13,X12),X16)
      | ~ v1_relat_1(X17)
      | ~ v1_relat_1(X12)
      | ~ r1_tarski(X17,X13) ) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,(
    ! [X14,X12,X17,X15,X13,X16] :
      ( ~ v1_relat_1(X12)
      | ~ v1_relat_1(X13)
      | r2_hidden(k4_tarski(X14,X15),X16)
      | ~ r1_tarski(k5_relat_1(X13,X12),X16)
      | ~ v1_relat_1(X17)
      | ~ r2_hidden(k4_tarski(X14,X15),k5_relat_1(X17,X12))
      | ~ v1_relat_1(X17)
      | ~ r2_hidden(k4_tarski(X14,X15),k5_relat_1(X17,X12))
      | ~ v1_relat_1(X12)
      | ~ r1_tarski(X17,X13) ) ),
    inference(resolution,[],[f96,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X2,sK5(X1,X0,X2,X3)),X4)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X4) ) ),
    inference(subsumption_resolution,[],[f76,f26])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | r2_hidden(k4_tarski(X2,sK5(X1,X0,X2,X3)),X4)
      | ~ r1_tarski(X1,X4) ) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(X2,sK5(X1,X0,X2,X3)),X4)
      | ~ r1_tarski(X1,X4) ) ),
    inference(resolution,[],[f29,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK5(X0,X1,X3,X4)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f96,plain,(
    ! [X24,X23,X21,X19,X22,X20,X18] :
      ( ~ r2_hidden(k4_tarski(X18,sK5(X19,X20,X21,X22)),X23)
      | ~ v1_relat_1(X20)
      | ~ v1_relat_1(X23)
      | r2_hidden(k4_tarski(X18,X22),X24)
      | ~ r1_tarski(k5_relat_1(X23,X20),X24)
      | ~ v1_relat_1(X19)
      | ~ r2_hidden(k4_tarski(X21,X22),k5_relat_1(X19,X20)) ) ),
    inference(subsumption_resolution,[],[f94,f26])).

fof(f94,plain,(
    ! [X24,X23,X21,X19,X22,X20,X18] :
      ( ~ r2_hidden(k4_tarski(X18,sK5(X19,X20,X21,X22)),X23)
      | ~ v1_relat_1(X20)
      | ~ v1_relat_1(X23)
      | r2_hidden(k4_tarski(X18,X22),X24)
      | ~ r1_tarski(k5_relat_1(X23,X20),X24)
      | ~ v1_relat_1(k5_relat_1(X19,X20))
      | ~ v1_relat_1(X19)
      | ~ r2_hidden(k4_tarski(X21,X22),k5_relat_1(X19,X20)) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X24,X23,X21,X19,X22,X20,X18] :
      ( ~ r2_hidden(k4_tarski(X18,sK5(X19,X20,X21,X22)),X23)
      | ~ v1_relat_1(X20)
      | ~ v1_relat_1(X23)
      | r2_hidden(k4_tarski(X18,X22),X24)
      | ~ r1_tarski(k5_relat_1(X23,X20),X24)
      | ~ v1_relat_1(X20)
      | ~ v1_relat_1(k5_relat_1(X19,X20))
      | ~ v1_relat_1(X19)
      | ~ r2_hidden(k4_tarski(X21,X22),k5_relat_1(X19,X20)) ) ),
    inference(resolution,[],[f83,f28])).

fof(f28,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f83,plain,(
    ! [X6,X4,X8,X7,X5,X9] :
      ( ~ r2_hidden(k4_tarski(X7,X8),X4)
      | ~ r2_hidden(k4_tarski(X6,X7),X5)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | r2_hidden(k4_tarski(X6,X8),X9)
      | ~ r1_tarski(k5_relat_1(X5,X4),X9) ) ),
    inference(subsumption_resolution,[],[f81,f26])).

fof(f81,plain,(
    ! [X6,X4,X8,X7,X5,X9] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(k5_relat_1(X5,X4))
      | ~ r2_hidden(k4_tarski(X6,X7),X5)
      | ~ r2_hidden(k4_tarski(X7,X8),X4)
      | ~ v1_relat_1(X5)
      | r2_hidden(k4_tarski(X6,X8),X9)
      | ~ r1_tarski(k5_relat_1(X5,X4),X9) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X6,X4,X8,X7,X5,X9] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(k5_relat_1(X5,X4))
      | ~ r2_hidden(k4_tarski(X6,X7),X5)
      | ~ r2_hidden(k4_tarski(X7,X8),X4)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(k5_relat_1(X5,X4))
      | r2_hidden(k4_tarski(X6,X8),X9)
      | ~ r1_tarski(k5_relat_1(X5,X4),X9) ) ),
    inference(resolution,[],[f27,f23])).

fof(f27,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f370,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_5 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_5 ),
    inference(unit_resulting_resolution,[],[f38,f43,f33,f48,f53,f361])).

fof(f54,plain,(
    ~ spl9_5 ),
    inference(avatar_split_clause,[],[f14,f51])).

fof(f14,plain,(
    ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              & r1_tarski(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              & r1_tarski(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ( r1_tarski(X0,X1)
                 => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relat_1)).

fof(f49,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f13,f46])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f16,f41])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f39,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f15,f36])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f12,f31])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------

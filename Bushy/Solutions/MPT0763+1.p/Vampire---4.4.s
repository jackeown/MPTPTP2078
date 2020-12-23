%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t9_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:16 EDT 2019

% Result     : Theorem 5.99s
% Output     : Refutation 5.99s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 423 expanded)
%              Number of leaves         :   50 ( 178 expanded)
%              Depth                    :   11
%              Number of atoms          :  823 (1991 expanded)
%              Number of equality atoms :   99 ( 215 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4803,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f134,f138,f142,f233,f238,f246,f284,f776,f1372,f1466,f1498,f1502,f1613,f2373,f3154,f4626,f4643,f4720,f4736,f4787,f4802])).

fof(f4802,plain,
    ( ~ spl12_887
    | ~ spl12_2
    | ~ spl12_926 ),
    inference(avatar_split_clause,[],[f4800,f4785,f132,f4595])).

fof(f4595,plain,
    ( spl12_887
  <=> ~ r1_wellord1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_887])])).

fof(f132,plain,
    ( spl12_2
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f4785,plain,
    ( spl12_926
  <=> ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_wellord1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_926])])).

fof(f4800,plain,
    ( ~ r1_wellord1(sK1,sK0)
    | ~ spl12_2
    | ~ spl12_926 ),
    inference(resolution,[],[f4786,f133])).

fof(f133,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f132])).

fof(f4786,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_wellord1(sK1,X0) )
    | ~ spl12_926 ),
    inference(avatar_component_clause,[],[f4785])).

fof(f4787,plain,
    ( spl12_0
    | spl12_926
    | ~ spl12_6
    | spl12_901 ),
    inference(avatar_split_clause,[],[f4779,f4641,f140,f4785,f236])).

fof(f236,plain,
    ( spl12_0
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f140,plain,
    ( spl12_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f4641,plain,
    ( spl12_901
  <=> ~ r1_xboole_0(k1_wellord1(sK1,sK6(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_901])])).

fof(f4779,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_wellord1(sK1,X0)
        | k1_xboole_0 = sK2 )
    | ~ spl12_6
    | ~ spl12_901 ),
    inference(resolution,[],[f4642,f1145])).

fof(f1145,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_wellord1(sK1,sK6(sK1,X0)),X0)
        | ~ r1_tarski(X0,X1)
        | ~ r1_wellord1(sK1,X1)
        | k1_xboole_0 = X0 )
    | ~ spl12_6 ),
    inference(resolution,[],[f86,f141])).

fof(f141,plain,
    ( v1_relat_1(sK1)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f140])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = X4
      | ~ r1_tarski(X4,X1)
      | ~ r1_wellord1(X0,X1)
      | r1_xboole_0(k1_wellord1(X0,sK6(X0,X4)),X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_wellord1(X0,X1)
            | ( ! [X3] :
                  ( ~ r1_xboole_0(k1_wellord1(X0,X3),sK5(X0,X1))
                  | ~ r2_hidden(X3,sK5(X0,X1)) )
              & k1_xboole_0 != sK5(X0,X1)
              & r1_tarski(sK5(X0,X1),X1) ) )
          & ( ! [X4] :
                ( ( r1_xboole_0(k1_wellord1(X0,sK6(X0,X4)),X4)
                  & r2_hidden(sK6(X0,X4),X4) )
                | k1_xboole_0 = X4
                | ~ r1_tarski(X4,X1) )
            | ~ r1_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f55,f57,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_xboole_0(k1_wellord1(X0,X3),X2)
              | ~ r2_hidden(X3,X2) )
          & k1_xboole_0 != X2
          & r1_tarski(X2,X1) )
     => ( ! [X3] :
            ( ~ r1_xboole_0(k1_wellord1(X0,X3),sK5(X0,X1))
            | ~ r2_hidden(X3,sK5(X0,X1)) )
        & k1_xboole_0 != sK5(X0,X1)
        & r1_tarski(sK5(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( r1_xboole_0(k1_wellord1(X0,X5),X4)
          & r2_hidden(X5,X4) )
     => ( r1_xboole_0(k1_wellord1(X0,sK6(X0,X4)),X4)
        & r2_hidden(sK6(X0,X4),X4) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/wellord1__t9_wellord1.p',d3_wellord1)).

fof(f4642,plain,
    ( ~ r1_xboole_0(k1_wellord1(sK1,sK6(sK1,sK2)),sK2)
    | ~ spl12_901 ),
    inference(avatar_component_clause,[],[f4641])).

fof(f4736,plain,
    ( ~ spl12_207
    | ~ spl12_4
    | ~ spl12_118
    | spl12_913 ),
    inference(avatar_split_clause,[],[f4723,f4718,f774,f136,f3149])).

fof(f3149,plain,
    ( spl12_207
  <=> ~ r2_hidden(sK6(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_207])])).

fof(f136,plain,
    ( spl12_4
  <=> r2_wellord1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f774,plain,
    ( spl12_118
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,X3)
        | ~ r2_wellord1(sK1,X3)
        | r2_hidden(k4_tarski(X2,X2),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_118])])).

fof(f4718,plain,
    ( spl12_913
  <=> ~ r2_hidden(k4_tarski(sK6(sK1,sK2),sK6(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_913])])).

fof(f4723,plain,
    ( ~ r2_hidden(sK6(sK1,sK2),sK0)
    | ~ spl12_4
    | ~ spl12_118
    | ~ spl12_913 ),
    inference(resolution,[],[f4719,f777])).

fof(f777,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,X0),sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl12_4
    | ~ spl12_118 ),
    inference(resolution,[],[f775,f137])).

fof(f137,plain,
    ( r2_wellord1(sK1,sK0)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f136])).

fof(f775,plain,
    ( ! [X2,X3] :
        ( ~ r2_wellord1(sK1,X3)
        | ~ r2_hidden(X2,X3)
        | r2_hidden(k4_tarski(X2,X2),sK1) )
    | ~ spl12_118 ),
    inference(avatar_component_clause,[],[f774])).

fof(f4719,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK1,sK2),sK6(sK1,sK2)),sK1)
    | ~ spl12_913 ),
    inference(avatar_component_clause,[],[f4718])).

fof(f4720,plain,
    ( ~ spl12_205
    | ~ spl12_913
    | ~ spl12_550 ),
    inference(avatar_split_clause,[],[f4713,f3146,f4718,f4715])).

fof(f4715,plain,
    ( spl12_205
  <=> ~ r2_hidden(sK6(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_205])])).

fof(f3146,plain,
    ( spl12_550
  <=> sK3(sK6(sK1,sK2)) = sK6(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_550])])).

fof(f4713,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK1,sK2),sK6(sK1,sK2)),sK1)
    | ~ r2_hidden(sK6(sK1,sK2),sK2)
    | ~ spl12_550 ),
    inference(superposition,[],[f80,f3147])).

fof(f3147,plain,
    ( sK3(sK6(sK1,sK2)) = sK6(sK1,sK2)
    | ~ spl12_550 ),
    inference(avatar_component_clause,[],[f3146])).

fof(f80,plain,(
    ! [X3] :
      ( ~ r2_hidden(k4_tarski(X3,sK3(X3)),sK1)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ! [X3] :
        ( ( ~ r2_hidden(k4_tarski(X3,sK3(X3)),sK1)
          & r2_hidden(sK3(X3),sK2) )
        | ~ r2_hidden(X3,sK2) )
    & k1_xboole_0 != sK2
    & r1_tarski(sK2,sK0)
    & r2_wellord1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    & r2_hidden(X4,X2) )
                | ~ r2_hidden(X3,X2) )
            & k1_xboole_0 != X2
            & r1_tarski(X2,X0) )
        & r2_wellord1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),sK1)
                  & r2_hidden(X4,X2) )
              | ~ r2_hidden(X3,X2) )
          & k1_xboole_0 != X2
          & r1_tarski(X2,sK0) )
      & r2_wellord1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X2) )
              | ~ r2_hidden(X3,X2) )
          & k1_xboole_0 != X2
          & r1_tarski(X2,X0) )
     => ( ! [X3] :
            ( ? [X4] :
                ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(X4,sK2) )
            | ~ r2_hidden(X3,sK2) )
        & k1_xboole_0 != sK2
        & r1_tarski(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X1,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(k4_tarski(X3,X4),X1)
          & r2_hidden(X4,X2) )
     => ( ~ r2_hidden(k4_tarski(X3,sK3(X3)),X1)
        & r2_hidden(sK3(X3),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X2) )
              | ~ r2_hidden(X3,X2) )
          & k1_xboole_0 != X2
          & r1_tarski(X2,X0) )
      & r2_wellord1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X2) )
              | ~ r2_hidden(X3,X2) )
          & k1_xboole_0 != X2
          & r1_tarski(X2,X0) )
      & r2_wellord1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_wellord1(X1,X0)
         => ! [X2] :
              ~ ( ! [X3] :
                    ~ ( ! [X4] :
                          ( r2_hidden(X4,X2)
                         => r2_hidden(k4_tarski(X3,X4),X1) )
                      & r2_hidden(X3,X2) )
                & k1_xboole_0 != X2
                & r1_tarski(X2,X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_wellord1(X1,X0)
       => ! [X2] :
            ~ ( ! [X3] :
                  ~ ( ! [X4] :
                        ( r2_hidden(X4,X2)
                       => r2_hidden(k4_tarski(X3,X4),X1) )
                    & r2_hidden(X3,X2) )
              & k1_xboole_0 != X2
              & r1_tarski(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t9_wellord1.p',t9_wellord1)).

fof(f4643,plain,
    ( ~ spl12_901
    | ~ spl12_204
    | ~ spl12_548 ),
    inference(avatar_split_clause,[],[f4629,f3143,f1464,f4641])).

fof(f1464,plain,
    ( spl12_204
  <=> r2_hidden(sK6(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_204])])).

fof(f3143,plain,
    ( spl12_548
  <=> r2_hidden(sK3(sK6(sK1,sK2)),k1_wellord1(sK1,sK6(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_548])])).

fof(f4629,plain,
    ( ~ r1_xboole_0(k1_wellord1(sK1,sK6(sK1,sK2)),sK2)
    | ~ spl12_204
    | ~ spl12_548 ),
    inference(resolution,[],[f3144,f1467])).

fof(f1467,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK6(sK1,sK2)),X0)
        | ~ r1_xboole_0(X0,sK2) )
    | ~ spl12_204 ),
    inference(resolution,[],[f1465,f166])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(sK3(X1),X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f112,f79])).

fof(f79,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK2)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f35,f72])).

fof(f72,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t9_wellord1.p',t3_xboole_0)).

fof(f1465,plain,
    ( r2_hidden(sK6(sK1,sK2),sK2)
    | ~ spl12_204 ),
    inference(avatar_component_clause,[],[f1464])).

fof(f3144,plain,
    ( r2_hidden(sK3(sK6(sK1,sK2)),k1_wellord1(sK1,sK6(sK1,sK2)))
    | ~ spl12_548 ),
    inference(avatar_component_clause,[],[f3143])).

fof(f4626,plain,
    ( ~ spl12_7
    | ~ spl12_5
    | spl12_887 ),
    inference(avatar_split_clause,[],[f4606,f4595,f4624,f767])).

fof(f767,plain,
    ( spl12_7
  <=> ~ v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f4624,plain,
    ( spl12_5
  <=> ~ r2_wellord1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f4606,plain,
    ( ~ r2_wellord1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl12_887 ),
    inference(resolution,[],[f4596,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_wellord1(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t9_wellord1.p',d5_wellord1)).

fof(f4596,plain,
    ( ~ r1_wellord1(sK1,sK0)
    | ~ spl12_887 ),
    inference(avatar_component_clause,[],[f4595])).

fof(f3154,plain,
    ( spl12_548
    | spl12_550
    | ~ spl12_207
    | ~ spl12_209
    | ~ spl12_204
    | ~ spl12_410 ),
    inference(avatar_split_clause,[],[f3136,f2371,f1464,f3152,f3149,f3146,f3143])).

fof(f3152,plain,
    ( spl12_209
  <=> ~ r2_hidden(sK3(sK6(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_209])])).

fof(f2371,plain,
    ( spl12_410
  <=> ! [X5,X6] :
        ( X5 = X6
        | r2_hidden(X6,k1_wellord1(sK1,X5))
        | ~ r2_hidden(X6,sK0)
        | ~ r2_hidden(X5,sK0)
        | r2_hidden(k4_tarski(X5,X6),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_410])])).

fof(f3136,plain,
    ( ~ r2_hidden(sK3(sK6(sK1,sK2)),sK0)
    | ~ r2_hidden(sK6(sK1,sK2),sK0)
    | sK3(sK6(sK1,sK2)) = sK6(sK1,sK2)
    | r2_hidden(sK3(sK6(sK1,sK2)),k1_wellord1(sK1,sK6(sK1,sK2)))
    | ~ spl12_204
    | ~ spl12_410 ),
    inference(resolution,[],[f2928,f1465])).

fof(f2928,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(sK3(X0),sK0)
        | ~ r2_hidden(X0,sK0)
        | sK3(X0) = X0
        | r2_hidden(sK3(X0),k1_wellord1(sK1,X0)) )
    | ~ spl12_410 ),
    inference(resolution,[],[f2372,f80])).

fof(f2372,plain,
    ( ! [X6,X5] :
        ( r2_hidden(k4_tarski(X5,X6),sK1)
        | r2_hidden(X6,k1_wellord1(sK1,X5))
        | ~ r2_hidden(X6,sK0)
        | ~ r2_hidden(X5,sK0)
        | X5 = X6 )
    | ~ spl12_410 ),
    inference(avatar_component_clause,[],[f2371])).

fof(f2373,plain,
    ( ~ spl12_7
    | spl12_410
    | ~ spl12_4
    | ~ spl12_240 ),
    inference(avatar_split_clause,[],[f2359,f1611,f136,f2371,f767])).

fof(f1611,plain,
    ( spl12_240
  <=> ! [X7,X8,X6] :
        ( X6 = X7
        | ~ r2_wellord1(sK1,X8)
        | r2_hidden(k4_tarski(X7,X6),sK1)
        | r2_hidden(k4_tarski(X6,X7),sK1)
        | ~ r2_hidden(X6,X8)
        | ~ r2_hidden(X7,X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_240])])).

fof(f2359,plain,
    ( ! [X6,X5] :
        ( X5 = X6
        | r2_hidden(k4_tarski(X5,X6),sK1)
        | ~ r2_hidden(X5,sK0)
        | ~ r2_hidden(X6,sK0)
        | r2_hidden(X6,k1_wellord1(sK1,X5))
        | ~ v1_relat_1(sK1) )
    | ~ spl12_4
    | ~ spl12_240 ),
    inference(duplicate_literal_removal,[],[f2351])).

fof(f2351,plain,
    ( ! [X6,X5] :
        ( X5 = X6
        | r2_hidden(k4_tarski(X5,X6),sK1)
        | ~ r2_hidden(X5,sK0)
        | ~ r2_hidden(X6,sK0)
        | r2_hidden(X6,k1_wellord1(sK1,X5))
        | X5 = X6
        | ~ v1_relat_1(sK1) )
    | ~ spl12_4
    | ~ spl12_240 ),
    inference(resolution,[],[f1846,f123])).

fof(f123,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X1),X0)
      | r2_hidden(X4,k1_wellord1(X0,X1))
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK9(X0,X1,X2),X1),X0)
                | sK9(X0,X1,X2) = X1
                | ~ r2_hidden(sK9(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK9(X0,X1,X2),X1),X0)
                  & sK9(X0,X1,X2) != X1 )
                | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f67,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK9(X0,X1,X2),X1),X0)
          | sK9(X0,X1,X2) = X1
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK9(X0,X1,X2),X1),X0)
            & sK9(X0,X1,X2) != X1 )
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
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
    inference(rectify,[],[f66])).

fof(f66,plain,(
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
    inference(flattening,[],[f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t9_wellord1.p',d1_wellord1)).

fof(f1846,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X1,X0),sK1)
        | X0 = X1
        | r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl12_4
    | ~ spl12_240 ),
    inference(resolution,[],[f1612,f137])).

fof(f1612,plain,
    ( ! [X6,X8,X7] :
        ( ~ r2_wellord1(sK1,X8)
        | X6 = X7
        | r2_hidden(k4_tarski(X7,X6),sK1)
        | r2_hidden(k4_tarski(X6,X7),sK1)
        | ~ r2_hidden(X6,X8)
        | ~ r2_hidden(X7,X8) )
    | ~ spl12_240 ),
    inference(avatar_component_clause,[],[f1611])).

fof(f1613,plain,
    ( ~ spl12_7
    | spl12_240
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f1601,f140,f1611,f767])).

fof(f1601,plain,
    ( ! [X6,X8,X7] :
        ( X6 = X7
        | ~ r2_hidden(X7,X8)
        | ~ r2_hidden(X6,X8)
        | r2_hidden(k4_tarski(X6,X7),sK1)
        | r2_hidden(k4_tarski(X7,X6),sK1)
        | ~ r2_wellord1(sK1,X8)
        | ~ v1_relat_1(sK1) )
    | ~ spl12_6 ),
    inference(resolution,[],[f1275,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r6_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f1275,plain,
    ( ! [X2,X0,X1] :
        ( ~ r6_relat_2(sK1,X2)
        | X0 = X1
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(k4_tarski(X1,X0),sK1) )
    | ~ spl12_6 ),
    inference(resolution,[],[f90,f141])).

fof(f90,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X4,X5),X0)
      | X4 = X5
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r6_relat_2(X0,X1)
      | r2_hidden(k4_tarski(X5,X4),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
              & ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
              & sK7(X0,X1) != sK8(X0,X1)
              & r2_hidden(sK8(X0,X1),X1)
              & r2_hidden(sK7(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | X4 = X5
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f60,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & X2 != X3
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
        & sK7(X0,X1) != sK8(X0,X1)
        & r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | X4 = X5
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X3,X2),X0)
                | r2_hidden(k4_tarski(X2,X3),X0)
                | X2 = X3
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r6_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | X2 = X3
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r6_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t9_wellord1.p',d6_relat_2)).

fof(f1502,plain,
    ( spl12_208
    | ~ spl12_2
    | spl12_25
    | ~ spl12_204 ),
    inference(avatar_split_clause,[],[f1485,f1464,f282,f132,f1500])).

fof(f1500,plain,
    ( spl12_208
  <=> r2_hidden(sK3(sK6(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_208])])).

fof(f282,plain,
    ( spl12_25
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).

fof(f1485,plain,
    ( r2_hidden(sK3(sK6(sK1,sK2)),sK0)
    | ~ spl12_2
    | ~ spl12_25
    | ~ spl12_204 ),
    inference(resolution,[],[f1465,f406])).

fof(f406,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(sK3(X0),sK0) )
    | ~ spl12_2
    | ~ spl12_25 ),
    inference(resolution,[],[f404,f79])).

fof(f404,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,sK0) )
    | ~ spl12_2
    | ~ spl12_25 ),
    inference(resolution,[],[f401,f285])).

fof(f285,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | r2_hidden(X0,sK0) )
    | ~ spl12_25 ),
    inference(resolution,[],[f283,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t9_wellord1.p',t2_subset)).

fof(f283,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl12_25 ),
    inference(avatar_component_clause,[],[f282])).

fof(f401,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK0)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl12_2 ),
    inference(resolution,[],[f385,f133])).

fof(f385,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X3)
      | ~ r2_hidden(X2,X4)
      | m1_subset_1(X2,X3) ) ),
    inference(resolution,[],[f121,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t9_wellord1.p',t3_subset)).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t9_wellord1.p',t4_subset)).

fof(f1498,plain,
    ( spl12_206
    | ~ spl12_2
    | spl12_25
    | ~ spl12_204 ),
    inference(avatar_split_clause,[],[f1484,f1464,f282,f132,f1496])).

fof(f1496,plain,
    ( spl12_206
  <=> r2_hidden(sK6(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_206])])).

fof(f1484,plain,
    ( r2_hidden(sK6(sK1,sK2),sK0)
    | ~ spl12_2
    | ~ spl12_25
    | ~ spl12_204 ),
    inference(resolution,[],[f1465,f404])).

fof(f1466,plain,
    ( spl12_0
    | spl12_204
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_178 ),
    inference(avatar_split_clause,[],[f1460,f1370,f136,f132,f1464,f236])).

fof(f1370,plain,
    ( spl12_178
  <=> ! [X3,X4] :
        ( ~ r1_tarski(X3,X4)
        | ~ r2_wellord1(sK1,X4)
        | r2_hidden(sK6(sK1,X3),X3)
        | k1_xboole_0 = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_178])])).

fof(f1460,plain,
    ( r2_hidden(sK6(sK1,sK2),sK2)
    | k1_xboole_0 = sK2
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_178 ),
    inference(resolution,[],[f1459,f133])).

fof(f1459,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r2_hidden(sK6(sK1,X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl12_4
    | ~ spl12_178 ),
    inference(resolution,[],[f1371,f137])).

fof(f1371,plain,
    ( ! [X4,X3] :
        ( ~ r2_wellord1(sK1,X4)
        | ~ r1_tarski(X3,X4)
        | r2_hidden(sK6(sK1,X3),X3)
        | k1_xboole_0 = X3 )
    | ~ spl12_178 ),
    inference(avatar_component_clause,[],[f1370])).

fof(f1372,plain,
    ( ~ spl12_7
    | spl12_178
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f1364,f140,f1370,f767])).

fof(f1364,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(X3,X4)
        | k1_xboole_0 = X3
        | r2_hidden(sK6(sK1,X3),X3)
        | ~ r2_wellord1(sK1,X4)
        | ~ v1_relat_1(sK1) )
    | ~ spl12_6 ),
    inference(resolution,[],[f755,f100])).

fof(f755,plain,
    ( ! [X0,X1] :
        ( ~ r1_wellord1(sK1,X1)
        | ~ r1_tarski(X0,X1)
        | k1_xboole_0 = X0
        | r2_hidden(sK6(sK1,X0),X0) )
    | ~ spl12_6 ),
    inference(resolution,[],[f85,f141])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = X4
      | ~ r1_tarski(X4,X1)
      | ~ r1_wellord1(X0,X1)
      | r2_hidden(sK6(X0,X4),X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f776,plain,
    ( ~ spl12_7
    | spl12_118
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f765,f140,f774,f767])).

fof(f765,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,X3)
        | r2_hidden(k4_tarski(X2,X2),sK1)
        | ~ r2_wellord1(sK1,X3)
        | ~ v1_relat_1(sK1) )
    | ~ spl12_6 ),
    inference(resolution,[],[f536,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f536,plain,
    ( ! [X0,X1] :
        ( ~ r1_relat_2(sK1,X1)
        | ~ r2_hidden(X0,X1)
        | r2_hidden(k4_tarski(X0,X0),sK1) )
    | ~ spl12_6 ),
    inference(resolution,[],[f82,f141])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,X1)
      | ~ r1_relat_2(X0,X1)
      | r2_hidden(k4_tarski(X3,X3),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK4(X0,X1)),X0)
              & r2_hidden(sK4(X0,X1),X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK4(X0,X1)),X0)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2] :
                ( r2_hidden(k4_tarski(X2,X2),X0)
                | ~ r2_hidden(X2,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t9_wellord1.p',d1_relat_2)).

fof(f284,plain,
    ( ~ spl12_25
    | ~ spl12_2
    | ~ spl12_18 ),
    inference(avatar_split_clause,[],[f279,f243,f132,f282])).

fof(f243,plain,
    ( spl12_18
  <=> r2_hidden(sK11(sK2,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f279,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl12_2
    | ~ spl12_18 ),
    inference(resolution,[],[f277,f133])).

fof(f277,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl12_18 ),
    inference(resolution,[],[f264,f118])).

fof(f264,plain,
    ( ! [X17] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X17))
        | ~ v1_xboole_0(X17) )
    | ~ spl12_18 ),
    inference(resolution,[],[f244,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t9_wellord1.p',t5_subset)).

fof(f244,plain,
    ( r2_hidden(sK11(sK2,sK2),sK2)
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f243])).

fof(f246,plain,
    ( spl12_18
    | spl12_17 ),
    inference(avatar_split_clause,[],[f240,f231,f243])).

fof(f231,plain,
    ( spl12_17
  <=> ~ r1_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).

fof(f240,plain,
    ( r2_hidden(sK11(sK2,sK2),sK2)
    | ~ spl12_17 ),
    inference(resolution,[],[f232,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f232,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | ~ spl12_17 ),
    inference(avatar_component_clause,[],[f231])).

fof(f238,plain,
    ( spl12_0
    | spl12_15 ),
    inference(avatar_split_clause,[],[f234,f228,f236])).

fof(f228,plain,
    ( spl12_15
  <=> ~ r2_hidden(sK10(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f234,plain,
    ( k1_xboole_0 = sK2
    | ~ spl12_15 ),
    inference(resolution,[],[f229,f185])).

fof(f185,plain,(
    ! [X0] :
      ( r2_hidden(sK10(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f165,f109])).

fof(f109,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f15,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK10(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t9_wellord1.p',existence_m1_subset_1)).

fof(f165,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,X4)
      | r2_hidden(X3,X4)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f114,f108])).

fof(f108,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t9_wellord1.p',t6_boole)).

fof(f229,plain,
    ( ~ r2_hidden(sK10(sK2),sK2)
    | ~ spl12_15 ),
    inference(avatar_component_clause,[],[f228])).

fof(f233,plain,
    ( ~ spl12_15
    | ~ spl12_17 ),
    inference(avatar_split_clause,[],[f226,f231,f228])).

fof(f226,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | ~ r2_hidden(sK10(sK2),sK2) ),
    inference(resolution,[],[f209,f79])).

fof(f209,plain,(
    ! [X6] :
      ( ~ r2_hidden(sK3(sK10(sK2)),X6)
      | ~ r1_xboole_0(X6,sK2) ) ),
    inference(global_subsumption,[],[f78,f192])).

fof(f192,plain,(
    ! [X6] :
      ( k1_xboole_0 = sK2
      | ~ r2_hidden(sK3(sK10(sK2)),X6)
      | ~ r1_xboole_0(X6,sK2) ) ),
    inference(resolution,[],[f185,f166])).

fof(f78,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f49])).

fof(f142,plain,(
    spl12_6 ),
    inference(avatar_split_clause,[],[f75,f140])).

fof(f75,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f138,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f76,f136])).

fof(f76,plain,(
    r2_wellord1(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f134,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f77,f132])).

fof(f77,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f130,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f78,f128])).

fof(f128,plain,
    ( spl12_1
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t9_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:29 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 306 expanded)
%              Number of leaves         :   27 ( 129 expanded)
%              Depth                    :   11
%              Number of atoms          :  504 (1492 expanded)
%              Number of equality atoms :   92 ( 387 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1283,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f96,f103,f110,f124,f131,f245,f249,f309,f327,f691,f718,f732,f864,f1171,f1195,f1200,f1231,f1279,f1282])).

fof(f1282,plain,
    ( spl8_200
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_126 ),
    inference(avatar_split_clause,[],[f1281,f683,f108,f101,f1169])).

fof(f1169,plain,
    ( spl8_200
  <=> k1_funct_1(sK1,sK2(sK0,sK1)) = sK3(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_200])])).

fof(f101,plain,
    ( spl8_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f108,plain,
    ( spl8_6
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f683,plain,
    ( spl8_126
  <=> r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_126])])).

fof(f1281,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_126 ),
    inference(subsumption_resolution,[],[f1280,f102])).

fof(f102,plain,
    ( v1_relat_1(sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f1280,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl8_6
    | ~ spl8_126 ),
    inference(subsumption_resolution,[],[f1202,f109])).

fof(f109,plain,
    ( v1_funct_1(sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f1202,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl8_126 ),
    inference(resolution,[],[f684,f195])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) = X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f61,f79])).

fof(f79,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f42,f45,f44,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t9_funct_1.p',d4_relat_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t9_funct_1.p',d4_funct_1)).

fof(f684,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | ~ spl8_126 ),
    inference(avatar_component_clause,[],[f683])).

fof(f1279,plain,
    ( spl8_154
    | ~ spl8_134
    | ~ spl8_200 ),
    inference(avatar_split_clause,[],[f1232,f1169,f716,f862])).

fof(f862,plain,
    ( spl8_154
  <=> k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_154])])).

fof(f716,plain,
    ( spl8_134
  <=> r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_134])])).

fof(f1232,plain,
    ( k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | ~ spl8_134
    | ~ spl8_200 ),
    inference(forward_demodulation,[],[f741,f1170])).

fof(f1170,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | ~ spl8_200 ),
    inference(avatar_component_clause,[],[f1169])).

fof(f741,plain,
    ( k1_funct_1(sK0,sK2(sK0,sK1)) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl8_134 ),
    inference(resolution,[],[f717,f52])).

fof(f52,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK0))
      | k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK0 != sK1
    & ! [X2] :
        ( k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2)
        | ~ r2_hidden(X2,k1_relat_1(sK0)) )
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) )
            & k1_relat_1(X0) = k1_relat_1(X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & ! [X2] :
              ( k1_funct_1(sK0,X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,k1_relat_1(sK0)) )
          & k1_relat_1(sK0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & ! [X2] :
              ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( sK1 != X0
        & ! [X2] :
            ( k1_funct_1(sK1,X2) = k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0)) )
        & k1_relat_1(sK1) = k1_relat_1(X0)
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & ! [X2] :
              ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & ! [X2] :
              ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( ! [X2] :
                    ( r2_hidden(X2,k1_relat_1(X0))
                   => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
                & k1_relat_1(X0) = k1_relat_1(X1) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t9_funct_1.p',t9_funct_1)).

fof(f717,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | ~ spl8_134 ),
    inference(avatar_component_clause,[],[f716])).

fof(f1231,plain,
    ( ~ spl8_36
    | spl8_129
    | ~ spl8_134
    | ~ spl8_154 ),
    inference(avatar_contradiction_clause,[],[f1230])).

fof(f1230,plain,
    ( $false
    | ~ spl8_36
    | ~ spl8_129
    | ~ spl8_134
    | ~ spl8_154 ),
    inference(subsumption_resolution,[],[f1201,f687])).

fof(f687,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | ~ spl8_129 ),
    inference(avatar_component_clause,[],[f686])).

fof(f686,plain,
    ( spl8_129
  <=> ~ r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_129])])).

fof(f1201,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | ~ spl8_36
    | ~ spl8_134
    | ~ spl8_154 ),
    inference(subsumption_resolution,[],[f912,f717])).

fof(f912,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | ~ spl8_36
    | ~ spl8_154 ),
    inference(superposition,[],[f244,f863])).

fof(f863,plain,
    ( k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | ~ spl8_154 ),
    inference(avatar_component_clause,[],[f862])).

fof(f244,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK0,X0)),sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl8_36
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK0,X0)),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f1200,plain,
    ( ~ spl8_127
    | ~ spl8_4
    | spl8_11
    | ~ spl8_52
    | ~ spl8_128 ),
    inference(avatar_split_clause,[],[f1198,f689,f325,f122,f101,f680])).

fof(f680,plain,
    ( spl8_127
  <=> ~ r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_127])])).

fof(f122,plain,
    ( spl8_11
  <=> sK0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f325,plain,
    ( spl8_52
  <=> ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),X0)
        | ~ r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),sK0)
        | ~ v1_relat_1(X0)
        | sK0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f689,plain,
    ( spl8_128
  <=> r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_128])])).

fof(f1198,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_52
    | ~ spl8_128 ),
    inference(subsumption_resolution,[],[f1197,f123])).

fof(f123,plain,
    ( sK0 != sK1
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f122])).

fof(f1197,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | sK0 = sK1
    | ~ spl8_4
    | ~ spl8_52
    | ~ spl8_128 ),
    inference(subsumption_resolution,[],[f719,f102])).

fof(f719,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | sK0 = sK1
    | ~ spl8_52
    | ~ spl8_128 ),
    inference(resolution,[],[f690,f326])).

fof(f326,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),sK0)
        | ~ r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),X0)
        | ~ v1_relat_1(X0)
        | sK0 = X0 )
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f325])).

fof(f690,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | ~ spl8_128 ),
    inference(avatar_component_clause,[],[f689])).

fof(f1195,plain,
    ( ~ spl8_38
    | spl8_127
    | ~ spl8_134
    | ~ spl8_200 ),
    inference(avatar_contradiction_clause,[],[f1194])).

fof(f1194,plain,
    ( $false
    | ~ spl8_38
    | ~ spl8_127
    | ~ spl8_134
    | ~ spl8_200 ),
    inference(subsumption_resolution,[],[f1193,f717])).

fof(f1193,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | ~ spl8_38
    | ~ spl8_127
    | ~ spl8_200 ),
    inference(subsumption_resolution,[],[f1191,f681])).

fof(f681,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | ~ spl8_127 ),
    inference(avatar_component_clause,[],[f680])).

fof(f1191,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | ~ spl8_38
    | ~ spl8_200 ),
    inference(superposition,[],[f248,f1170])).

fof(f248,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(X1,k1_funct_1(sK1,X1)),sK1)
        | ~ r2_hidden(X1,k1_relat_1(sK0)) )
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl8_38
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK0))
        | r2_hidden(k4_tarski(X1,k1_funct_1(sK1,X1)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f1171,plain,
    ( spl8_200
    | ~ spl8_134
    | ~ spl8_154 ),
    inference(avatar_split_clause,[],[f1160,f862,f716,f1169])).

fof(f1160,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | ~ spl8_134
    | ~ spl8_154 ),
    inference(forward_demodulation,[],[f741,f863])).

fof(f864,plain,
    ( spl8_154
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_128 ),
    inference(avatar_split_clause,[],[f725,f689,f94,f87,f862])).

fof(f87,plain,
    ( spl8_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f94,plain,
    ( spl8_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f725,plain,
    ( k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_128 ),
    inference(subsumption_resolution,[],[f724,f88])).

fof(f88,plain,
    ( v1_relat_1(sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f87])).

fof(f724,plain,
    ( k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl8_2
    | ~ spl8_128 ),
    inference(subsumption_resolution,[],[f720,f95])).

fof(f95,plain,
    ( v1_funct_1(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f720,plain,
    ( k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl8_128 ),
    inference(resolution,[],[f690,f195])).

fof(f732,plain,
    ( spl8_134
    | ~ spl8_128 ),
    inference(avatar_split_clause,[],[f721,f689,f716])).

fof(f721,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | ~ spl8_128 ),
    inference(resolution,[],[f690,f79])).

fof(f718,plain,
    ( spl8_134
    | ~ spl8_12
    | ~ spl8_126 ),
    inference(avatar_split_clause,[],[f698,f683,f129,f716])).

fof(f129,plain,
    ( spl8_12
  <=> k1_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f698,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | ~ spl8_12
    | ~ spl8_126 ),
    inference(forward_demodulation,[],[f693,f130])).

fof(f130,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f693,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ spl8_126 ),
    inference(resolution,[],[f684,f79])).

fof(f691,plain,
    ( spl8_126
    | spl8_128
    | ~ spl8_4
    | spl8_11
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f340,f307,f122,f101,f689,f683])).

fof(f307,plain,
    ( spl8_46
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),X0)
        | r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),sK0)
        | ~ v1_relat_1(X0)
        | sK0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f340,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f338,f123])).

fof(f338,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | sK0 = sK1
    | ~ spl8_4
    | ~ spl8_46 ),
    inference(resolution,[],[f308,f102])).

fof(f308,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),sK0)
        | r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),X0)
        | sK0 = X0 )
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f307])).

fof(f327,plain,
    ( spl8_52
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f220,f87,f325])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),X0)
        | ~ r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),sK0)
        | ~ v1_relat_1(X0)
        | sK0 = X0 )
    | ~ spl8_0 ),
    inference(resolution,[],[f58,f88])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t9_funct_1.p',d2_relat_1)).

fof(f309,plain,
    ( spl8_46
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f214,f87,f307])).

fof(f214,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),X0)
        | r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),sK0)
        | ~ v1_relat_1(X0)
        | sK0 = X0 )
    | ~ spl8_0 ),
    inference(resolution,[],[f57,f88])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f249,plain,
    ( spl8_38
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f178,f129,f108,f101,f247])).

fof(f178,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK0))
        | r2_hidden(k4_tarski(X1,k1_funct_1(sK1,X1)),sK1) )
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f177,f130])).

fof(f177,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X1,k1_funct_1(sK1,X1)),sK1) )
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f175,f102])).

fof(f175,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X1,k1_funct_1(sK1,X1)),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl8_6 ),
    inference(resolution,[],[f78,f109])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f245,plain,
    ( spl8_36
    | ~ spl8_0
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f176,f94,f87,f243])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK0,X0)),sK0) )
    | ~ spl8_0
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f174,f88])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK0,X0)),sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f78,f95])).

fof(f131,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f51,f129])).

fof(f51,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f124,plain,(
    ~ spl8_11 ),
    inference(avatar_split_clause,[],[f53,f122])).

fof(f53,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f110,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f50,f108])).

fof(f50,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f103,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f49,f101])).

fof(f49,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f96,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f48,f94])).

fof(f48,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f47,f87])).

fof(f47,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------

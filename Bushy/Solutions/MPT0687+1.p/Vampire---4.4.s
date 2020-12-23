%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t142_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:15 EDT 2019

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 217 expanded)
%              Number of leaves         :   34 (  92 expanded)
%              Depth                    :   11
%              Number of atoms          :  472 ( 894 expanded)
%              Number of equality atoms :  103 ( 197 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1085,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f104,f121,f133,f154,f156,f230,f298,f351,f679,f707,f726,f966,f993,f1023,f1051,f1072,f1084])).

fof(f1084,plain,
    ( ~ spl11_10
    | ~ spl11_14
    | ~ spl11_126 ),
    inference(avatar_contradiction_clause,[],[f1083])).

fof(f1083,plain,
    ( $false
    | ~ spl11_10
    | ~ spl11_14
    | ~ spl11_126 ),
    inference(subsumption_resolution,[],[f1082,f132])).

fof(f132,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl11_10
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f1082,plain,
    ( r2_hidden(sK10(sK1,sK0),k1_xboole_0)
    | ~ spl11_14
    | ~ spl11_126 ),
    inference(forward_demodulation,[],[f1078,f150])).

fof(f150,plain,
    ( k10_relat_1(sK1,k1_tarski(sK0)) = k1_xboole_0
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl11_14
  <=> k10_relat_1(sK1,k1_tarski(sK0)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f1078,plain,
    ( r2_hidden(sK10(sK1,sK0),k10_relat_1(sK1,k1_tarski(sK0)))
    | ~ spl11_126 ),
    inference(resolution,[],[f1071,f87])).

fof(f87,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t142_funct_1.p',d1_tarski)).

fof(f1071,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | r2_hidden(sK10(sK1,sK0),k10_relat_1(sK1,X0)) )
    | ~ spl11_126 ),
    inference(avatar_component_clause,[],[f1070])).

fof(f1070,plain,
    ( spl11_126
  <=> ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | r2_hidden(sK10(sK1,sK0),k10_relat_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_126])])).

fof(f1072,plain,
    ( spl11_126
    | ~ spl11_24
    | ~ spl11_120 ),
    inference(avatar_split_clause,[],[f1052,f1049,f228,f1070])).

fof(f228,plain,
    ( spl11_24
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(k4_tarski(X2,X0),sK1)
        | r2_hidden(X2,k10_relat_1(sK1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f1049,plain,
    ( spl11_120
  <=> r2_hidden(k4_tarski(sK10(sK1,sK0),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_120])])).

fof(f1052,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | r2_hidden(sK10(sK1,sK0),k10_relat_1(sK1,X0)) )
    | ~ spl11_24
    | ~ spl11_120 ),
    inference(resolution,[],[f1050,f229])).

fof(f229,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X2,X0),sK1)
        | ~ r2_hidden(X0,X1)
        | r2_hidden(X2,k10_relat_1(sK1,X1)) )
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f228])).

fof(f1050,plain,
    ( r2_hidden(k4_tarski(sK10(sK1,sK0),sK0),sK1)
    | ~ spl11_120 ),
    inference(avatar_component_clause,[],[f1049])).

fof(f1051,plain,
    ( spl11_120
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f1025,f146,f1049])).

fof(f146,plain,
    ( spl11_12
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f1025,plain,
    ( r2_hidden(k4_tarski(sK10(sK1,sK0),sK0),sK1)
    | ~ spl11_12 ),
    inference(resolution,[],[f147,f90])).

fof(f90,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK10(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK10(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK8(X0,X1)),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK10(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f51,f54,f53,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK8(X0,X1)),X0)
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK8(X0,X1)),X0)
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK9(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK10(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t142_funct_1.p',d5_relat_1)).

fof(f147,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f1023,plain,
    ( spl11_13
    | spl11_15
    | ~ spl11_114 ),
    inference(avatar_contradiction_clause,[],[f1022])).

fof(f1022,plain,
    ( $false
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_114 ),
    inference(subsumption_resolution,[],[f1017,f153])).

fof(f153,plain,
    ( k10_relat_1(sK1,k1_tarski(sK0)) != k1_xboole_0
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl11_15
  <=> k10_relat_1(sK1,k1_tarski(sK0)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f1017,plain,
    ( k10_relat_1(sK1,k1_tarski(sK0)) = k1_xboole_0
    | ~ spl11_13
    | ~ spl11_114 ),
    inference(resolution,[],[f992,f144])).

fof(f144,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl11_13
  <=> ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f992,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k2_relat_1(sK1))
        | k10_relat_1(sK1,k1_tarski(X1)) = k1_xboole_0 )
    | ~ spl11_114 ),
    inference(avatar_component_clause,[],[f991])).

fof(f991,plain,
    ( spl11_114
  <=> ! [X1] :
        ( r2_hidden(X1,k2_relat_1(sK1))
        | k10_relat_1(sK1,k1_tarski(X1)) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_114])])).

fof(f993,plain,
    ( spl11_114
    | ~ spl11_86
    | ~ spl11_102 ),
    inference(avatar_split_clause,[],[f987,f821,f705,f991])).

fof(f705,plain,
    ( spl11_86
  <=> ! [X15] :
        ( r2_hidden(sK3(sK1,X15,k1_xboole_0),k2_relat_1(sK1))
        | k10_relat_1(sK1,X15) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_86])])).

fof(f821,plain,
    ( spl11_102
  <=> ! [X3] :
        ( k10_relat_1(sK1,k1_tarski(X3)) = k1_xboole_0
        | sK3(sK1,k1_tarski(X3),k1_xboole_0) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_102])])).

fof(f987,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k2_relat_1(sK1))
        | k10_relat_1(sK1,k1_tarski(X1)) = k1_xboole_0 )
    | ~ spl11_86
    | ~ spl11_102 ),
    inference(duplicate_literal_removal,[],[f976])).

fof(f976,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k2_relat_1(sK1))
        | k10_relat_1(sK1,k1_tarski(X1)) = k1_xboole_0
        | k10_relat_1(sK1,k1_tarski(X1)) = k1_xboole_0 )
    | ~ spl11_86
    | ~ spl11_102 ),
    inference(superposition,[],[f706,f822])).

fof(f822,plain,
    ( ! [X3] :
        ( sK3(sK1,k1_tarski(X3),k1_xboole_0) = X3
        | k10_relat_1(sK1,k1_tarski(X3)) = k1_xboole_0 )
    | ~ spl11_102 ),
    inference(avatar_component_clause,[],[f821])).

fof(f706,plain,
    ( ! [X15] :
        ( r2_hidden(sK3(sK1,X15,k1_xboole_0),k2_relat_1(sK1))
        | k10_relat_1(sK1,X15) = k1_xboole_0 )
    | ~ spl11_86 ),
    inference(avatar_component_clause,[],[f705])).

fof(f966,plain,
    ( spl11_102
    | ~ spl11_10
    | ~ spl11_90 ),
    inference(avatar_split_clause,[],[f742,f724,f131,f821])).

fof(f724,plain,
    ( spl11_90
  <=> ! [X5,X4] :
        ( r2_hidden(sK2(sK1,k1_tarski(X4),X5),X5)
        | k10_relat_1(sK1,k1_tarski(X4)) = X5
        | sK3(sK1,k1_tarski(X4),X5) = X4 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_90])])).

fof(f742,plain,
    ( ! [X15] :
        ( k10_relat_1(sK1,k1_tarski(X15)) = k1_xboole_0
        | sK3(sK1,k1_tarski(X15),k1_xboole_0) = X15 )
    | ~ spl11_10
    | ~ spl11_90 ),
    inference(resolution,[],[f725,f132])).

fof(f725,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK2(sK1,k1_tarski(X4),X5),X5)
        | k10_relat_1(sK1,k1_tarski(X4)) = X5
        | sK3(sK1,k1_tarski(X4),X5) = X4 )
    | ~ spl11_90 ),
    inference(avatar_component_clause,[],[f724])).

fof(f726,plain,
    ( spl11_90
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f304,f296,f724])).

fof(f296,plain,
    ( spl11_34
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(sK1,X0,X1),X0)
        | r2_hidden(sK2(sK1,X0,X1),X1)
        | k10_relat_1(sK1,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f304,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK2(sK1,k1_tarski(X4),X5),X5)
        | k10_relat_1(sK1,k1_tarski(X4)) = X5
        | sK3(sK1,k1_tarski(X4),X5) = X4 )
    | ~ spl11_34 ),
    inference(resolution,[],[f297,f88])).

fof(f88,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f297,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK1,X0,X1),X0)
        | r2_hidden(sK2(sK1,X0,X1),X1)
        | k10_relat_1(sK1,X0) = X1 )
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f296])).

fof(f707,plain,
    ( spl11_86
    | ~ spl11_10
    | ~ spl11_84 ),
    inference(avatar_split_clause,[],[f698,f677,f131,f705])).

fof(f677,plain,
    ( spl11_84
  <=> ! [X3,X4] :
        ( r2_hidden(sK2(sK1,X3,X4),X4)
        | k10_relat_1(sK1,X3) = X4
        | r2_hidden(sK3(sK1,X3,X4),k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_84])])).

fof(f698,plain,
    ( ! [X15] :
        ( r2_hidden(sK3(sK1,X15,k1_xboole_0),k2_relat_1(sK1))
        | k10_relat_1(sK1,X15) = k1_xboole_0 )
    | ~ spl11_10
    | ~ spl11_84 ),
    inference(resolution,[],[f678,f132])).

fof(f678,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK2(sK1,X3,X4),X4)
        | r2_hidden(sK3(sK1,X3,X4),k2_relat_1(sK1))
        | k10_relat_1(sK1,X3) = X4 )
    | ~ spl11_84 ),
    inference(avatar_component_clause,[],[f677])).

fof(f679,plain,
    ( spl11_84
    | ~ spl11_38 ),
    inference(avatar_split_clause,[],[f354,f349,f677])).

fof(f349,plain,
    ( spl11_38
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(sK2(sK1,X0,X1),sK3(sK1,X0,X1)),sK1)
        | r2_hidden(sK2(sK1,X0,X1),X1)
        | k10_relat_1(sK1,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f354,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK2(sK1,X3,X4),X4)
        | k10_relat_1(sK1,X3) = X4
        | r2_hidden(sK3(sK1,X3,X4),k2_relat_1(sK1)) )
    | ~ spl11_38 ),
    inference(resolution,[],[f350,f89])).

fof(f89,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f350,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK2(sK1,X0,X1),sK3(sK1,X0,X1)),sK1)
        | r2_hidden(sK2(sK1,X0,X1),X1)
        | k10_relat_1(sK1,X0) = X1 )
    | ~ spl11_38 ),
    inference(avatar_component_clause,[],[f349])).

fof(f351,plain,
    ( spl11_38
    | ~ spl11_0 ),
    inference(avatar_split_clause,[],[f195,f95,f349])).

fof(f95,plain,
    ( spl11_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK2(sK1,X0,X1),sK3(sK1,X0,X1)),sK1)
        | r2_hidden(sK2(sK1,X0,X1),X1)
        | k10_relat_1(sK1,X0) = X1 )
    | ~ spl11_0 ),
    inference(resolution,[],[f63,f96])).

fof(f96,plain,
    ( v1_relat_1(sK1)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f95])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f38,f37,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t142_funct_1.p',d14_relat_1)).

fof(f298,plain,
    ( spl11_34
    | ~ spl11_0 ),
    inference(avatar_split_clause,[],[f194,f95,f296])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK1,X0,X1),X0)
        | r2_hidden(sK2(sK1,X0,X1),X1)
        | k10_relat_1(sK1,X0) = X1 )
    | ~ spl11_0 ),
    inference(resolution,[],[f64,f96])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f230,plain,
    ( spl11_24
    | ~ spl11_0 ),
    inference(avatar_split_clause,[],[f173,f95,f228])).

fof(f173,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(k4_tarski(X2,X0),sK1)
        | r2_hidden(X2,k10_relat_1(sK1,X1)) )
    | ~ spl11_0 ),
    inference(resolution,[],[f83,f96])).

fof(f83,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | r2_hidden(X6,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f156,plain,
    ( ~ spl11_13
    | spl11_15 ),
    inference(avatar_split_clause,[],[f155,f152,f143])).

fof(f155,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f58,f153])).

fof(f58,plain,
    ( k10_relat_1(sK1,k1_tarski(sK0)) = k1_xboole_0
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( k10_relat_1(sK1,k1_tarski(sK0)) = k1_xboole_0
      | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
    & ( k10_relat_1(sK1,k1_tarski(sK0)) != k1_xboole_0
      | r2_hidden(sK0,k2_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ( k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k10_relat_1(sK1,k1_tarski(sK0)) = k1_xboole_0
        | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
      & ( k10_relat_1(sK1,k1_tarski(sK0)) != k1_xboole_0
        | r2_hidden(sK0,k2_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t142_funct_1.p',t142_funct_1)).

fof(f154,plain,
    ( spl11_12
    | ~ spl11_15 ),
    inference(avatar_split_clause,[],[f57,f152,f146])).

fof(f57,plain,
    ( k10_relat_1(sK1,k1_tarski(sK0)) != k1_xboole_0
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f133,plain,
    ( spl11_10
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f122,f119,f131])).

fof(f119,plain,
    ( spl11_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f122,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl11_6 ),
    inference(resolution,[],[f120,f67])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t142_funct_1.p',d1_xboole_0)).

fof(f120,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,
    ( spl11_6
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f107,f102,f119])).

fof(f102,plain,
    ( spl11_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f107,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl11_2 ),
    inference(backward_demodulation,[],[f105,f103])).

fof(f103,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f105,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl11_2 ),
    inference(resolution,[],[f66,f103])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t142_funct_1.p',t6_boole)).

fof(f104,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f59,f102])).

fof(f59,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t142_funct_1.p',dt_o_0_0_xboole_0)).

fof(f97,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f56,f95])).

fof(f56,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:34 EST 2020

% Result     : Theorem 2.32s
% Output     : Refutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 311 expanded)
%              Number of leaves         :   21 ( 108 expanded)
%              Depth                    :   11
%              Number of atoms          :  471 (1722 expanded)
%              Number of equality atoms :   38 ( 221 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2943,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f136,f137,f138,f140,f148,f150,f164,f449,f906,f907,f915,f979,f2856,f2876,f2877,f2942])).

fof(f2942,plain,
    ( ~ spl10_163
    | ~ spl10_83
    | spl10_9 ),
    inference(avatar_split_clause,[],[f2939,f152,f1168,f2870])).

fof(f2870,plain,
    ( spl10_163
  <=> r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_163])])).

fof(f1168,plain,
    ( spl10_83
  <=> r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_83])])).

fof(f152,plain,
    ( spl10_9
  <=> r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f2939,plain,
    ( ~ r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | spl10_9 ),
    inference(resolution,[],[f153,f66])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(sK8(X0,X1,X2),X0) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f153,plain,
    ( ~ r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | spl10_9 ),
    inference(avatar_component_clause,[],[f152])).

fof(f2877,plain,
    ( ~ spl10_10
    | spl10_163
    | ~ spl10_2
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f803,f161,f102,f2870,f156])).

fof(f156,plain,
    ( spl10_10
  <=> r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f102,plain,
    ( spl10_2
  <=> ! [X16,X17] :
        ( r2_hidden(X16,k10_relat_1(sK2,X17))
        | ~ r2_hidden(X16,k1_relat_1(sK2))
        | ~ r2_hidden(k1_funct_1(sK2,X16),X17) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f161,plain,
    ( spl10_11
  <=> r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f803,plain,
    ( r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ spl10_2
    | ~ spl10_11 ),
    inference(resolution,[],[f354,f163])).

fof(f163,plain,
    ( r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k3_xboole_0(sK0,sK1))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f161])).

fof(f354,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_hidden(k1_funct_1(sK2,X4),k3_xboole_0(X5,X6))
        | r2_hidden(X4,k10_relat_1(sK2,X5))
        | ~ r2_hidden(X4,k1_relat_1(sK2)) )
    | ~ spl10_2 ),
    inference(resolution,[],[f103,f68])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f103,plain,
    ( ! [X17,X16] :
        ( ~ r2_hidden(k1_funct_1(sK2,X16),X17)
        | ~ r2_hidden(X16,k1_relat_1(sK2))
        | r2_hidden(X16,k10_relat_1(sK2,X17)) )
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f2876,plain,
    ( ~ spl10_10
    | spl10_83
    | ~ spl10_2
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f821,f161,f102,f1168,f156])).

fof(f821,plain,
    ( r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ spl10_2
    | ~ spl10_11 ),
    inference(resolution,[],[f355,f163])).

fof(f355,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_hidden(k1_funct_1(sK2,X7),k3_xboole_0(X9,X8))
        | r2_hidden(X7,k10_relat_1(sK2,X8))
        | ~ r2_hidden(X7,k1_relat_1(sK2)) )
    | ~ spl10_2 ),
    inference(resolution,[],[f103,f67])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2856,plain,
    ( ~ spl10_3
    | ~ spl10_9
    | spl10_64 ),
    inference(avatar_contradiction_clause,[],[f2844])).

fof(f2844,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_9
    | spl10_64 ),
    inference(resolution,[],[f475,f978])).

fof(f978,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | spl10_64 ),
    inference(avatar_component_clause,[],[f976])).

fof(f976,plain,
    ( spl10_64
  <=> r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f475,plain,
    ( r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ spl10_3
    | ~ spl10_9 ),
    inference(resolution,[],[f154,f226])).

fof(f226,plain,
    ( ! [X12,X13,X11] :
        ( ~ r2_hidden(X11,k3_xboole_0(X13,k10_relat_1(sK2,X12)))
        | r2_hidden(k1_funct_1(sK2,X11),X12) )
    | ~ spl10_3 ),
    inference(resolution,[],[f107,f67])).

fof(f107,plain,
    ( ! [X19,X18] :
        ( ~ r2_hidden(X18,k10_relat_1(sK2,X19))
        | r2_hidden(k1_funct_1(sK2,X18),X19) )
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl10_3
  <=> ! [X18,X19] :
        ( r2_hidden(k1_funct_1(sK2,X18),X19)
        | ~ r2_hidden(X18,k10_relat_1(sK2,X19)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f154,plain,
    ( r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f152])).

fof(f979,plain,
    ( ~ spl10_58
    | ~ spl10_64
    | spl10_11 ),
    inference(avatar_split_clause,[],[f972,f161,f976,f910])).

fof(f910,plain,
    ( spl10_58
  <=> r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f972,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)
    | ~ r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | spl10_11 ),
    inference(resolution,[],[f162,f66])).

fof(f162,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k3_xboole_0(sK0,sK1))
    | spl10_11 ),
    inference(avatar_component_clause,[],[f161])).

fof(f915,plain,
    ( spl10_58
    | ~ spl10_3
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f476,f152,f106,f910])).

fof(f476,plain,
    ( r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)
    | ~ spl10_3
    | ~ spl10_9 ),
    inference(resolution,[],[f154,f225])).

fof(f225,plain,
    ( ! [X10,X8,X9] :
        ( ~ r2_hidden(X8,k3_xboole_0(k10_relat_1(sK2,X9),X10))
        | r2_hidden(k1_funct_1(sK2,X8),X9) )
    | ~ spl10_3 ),
    inference(resolution,[],[f107,f68])).

fof(f907,plain,
    ( ~ spl10_11
    | ~ spl10_10
    | ~ spl10_9
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f523,f114,f152,f156,f161])).

fof(f114,plain,
    ( spl10_5
  <=> ! [X29,X30] :
        ( sQ9_eqProxy(k10_relat_1(sK2,X29),X30)
        | ~ r2_hidden(sK6(sK2,X29,X30),X30)
        | ~ r2_hidden(sK6(sK2,X29,X30),k1_relat_1(sK2))
        | ~ r2_hidden(k1_funct_1(sK2,sK6(sK2,X29,X30)),X29) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f523,plain,
    ( ~ r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k3_xboole_0(sK0,sK1))
    | ~ spl10_5 ),
    inference(resolution,[],[f115,f70])).

fof(f70,plain,(
    ~ sQ9_eqProxy(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    inference(equality_proxy_replacement,[],[f37,f69])).

fof(f69,plain,(
    ! [X1,X0] :
      ( sQ9_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ9_eqProxy])])).

fof(f37,plain,(
    k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k10_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

fof(f115,plain,
    ( ! [X30,X29] :
        ( sQ9_eqProxy(k10_relat_1(sK2,X29),X30)
        | ~ r2_hidden(sK6(sK2,X29,X30),X30)
        | ~ r2_hidden(sK6(sK2,X29,X30),k1_relat_1(sK2))
        | ~ r2_hidden(k1_funct_1(sK2,sK6(sK2,X29,X30)),X29) )
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f906,plain,
    ( ~ spl10_4
    | ~ spl10_9
    | spl10_10 ),
    inference(avatar_contradiction_clause,[],[f891])).

fof(f891,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_9
    | spl10_10 ),
    inference(resolution,[],[f477,f451])).

fof(f451,plain,
    ( ! [X0] : ~ r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,X0))
    | ~ spl10_4
    | spl10_10 ),
    inference(resolution,[],[f157,f111])).

fof(f111,plain,
    ( ! [X21,X20] :
        ( r2_hidden(X20,k1_relat_1(sK2))
        | ~ r2_hidden(X20,k10_relat_1(sK2,X21)) )
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl10_4
  <=> ! [X20,X21] :
        ( r2_hidden(X20,k1_relat_1(sK2))
        | ~ r2_hidden(X20,k10_relat_1(sK2,X21)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f157,plain,
    ( ~ r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | spl10_10 ),
    inference(avatar_component_clause,[],[f156])).

fof(f477,plain,
    ( r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))
    | ~ spl10_9 ),
    inference(resolution,[],[f154,f68])).

fof(f449,plain,
    ( spl10_10
    | spl10_9
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f427,f122,f152,f156])).

fof(f122,plain,
    ( spl10_7
  <=> ! [X34,X33] :
        ( sQ9_eqProxy(k10_relat_1(sK2,X33),X34)
        | r2_hidden(sK6(sK2,X33,X34),X34)
        | r2_hidden(sK6(sK2,X33,X34),k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f427,plain,
    ( r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ spl10_7 ),
    inference(resolution,[],[f123,f70])).

fof(f123,plain,
    ( ! [X33,X34] :
        ( sQ9_eqProxy(k10_relat_1(sK2,X33),X34)
        | r2_hidden(sK6(sK2,X33,X34),X34)
        | r2_hidden(sK6(sK2,X33,X34),k1_relat_1(sK2)) )
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f164,plain,
    ( ~ spl10_8
    | ~ spl10_1
    | spl10_9
    | spl10_11 ),
    inference(avatar_split_clause,[],[f142,f161,f152,f98,f132])).

fof(f132,plain,
    ( spl10_8
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f98,plain,
    ( spl10_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f142,plain,
    ( r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f70,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sQ9_eqProxy(k10_relat_1(X0,X1),X2)
      | r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f48,f69])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1)
                | ~ r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK6(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1)
                  & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1)
            & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(f150,plain,(
    spl10_8 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl10_8 ),
    inference(resolution,[],[f134,f35])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f134,plain,
    ( ~ v1_relat_1(sK2)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f132])).

fof(f148,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl10_1 ),
    inference(resolution,[],[f100,f36])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f100,plain,
    ( ~ v1_funct_1(sK2)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f140,plain,
    ( ~ spl10_8
    | spl10_5 ),
    inference(avatar_split_clause,[],[f130,f114,f132])).

fof(f130,plain,(
    ! [X10,X11] :
      ( sQ9_eqProxy(k10_relat_1(sK2,X10),X11)
      | ~ r2_hidden(k1_funct_1(sK2,sK6(sK2,X10,X11)),X10)
      | ~ r2_hidden(sK6(sK2,X10,X11),k1_relat_1(sK2))
      | ~ r2_hidden(sK6(sK2,X10,X11),X11)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f36,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sQ9_eqProxy(k10_relat_1(X0,X1),X2)
      | ~ r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))
      | ~ r2_hidden(sK6(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f49,f69])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))
      | ~ r2_hidden(sK6(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f138,plain,
    ( ~ spl10_8
    | spl10_7 ),
    inference(avatar_split_clause,[],[f128,f122,f132])).

fof(f128,plain,(
    ! [X6,X7] :
      ( sQ9_eqProxy(k10_relat_1(sK2,X6),X7)
      | r2_hidden(sK6(sK2,X6,X7),k1_relat_1(sK2))
      | r2_hidden(sK6(sK2,X6,X7),X7)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f36,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sQ9_eqProxy(k10_relat_1(X0,X1),X2)
      | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK6(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f47,f69])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK6(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f137,plain,
    ( ~ spl10_8
    | spl10_2 ),
    inference(avatar_split_clause,[],[f127,f102,f132])).

fof(f127,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,k10_relat_1(sK2,X5))
      | ~ r2_hidden(k1_funct_1(sK2,X4),X5)
      | ~ r2_hidden(X4,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f36,f63])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f136,plain,
    ( ~ spl10_8
    | spl10_3 ),
    inference(avatar_split_clause,[],[f126,f106,f132])).

fof(f126,plain,(
    ! [X2,X3] :
      ( r2_hidden(k1_funct_1(sK2,X2),X3)
      | ~ r2_hidden(X2,k10_relat_1(sK2,X3))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f36,f64])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f135,plain,
    ( ~ spl10_8
    | spl10_4 ),
    inference(avatar_split_clause,[],[f125,f110,f132])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(sK2))
      | ~ r2_hidden(X0,k10_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f36,f65])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (16254)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (16269)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (16259)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (16261)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.52  % (16260)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.52  % (16268)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.52  % (16266)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (16268)Refutation not found, incomplete strategy% (16268)------------------------------
% 0.20/0.53  % (16268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16268)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16268)Memory used [KB]: 10618
% 0.20/0.53  % (16268)Time elapsed: 0.088 s
% 0.20/0.53  % (16268)------------------------------
% 0.20/0.53  % (16268)------------------------------
% 0.20/0.53  % (16272)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.43/0.53  % (16264)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.43/0.54  % (16258)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.43/0.54  % (16263)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.43/0.55  % (16274)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.43/0.55  % (16257)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.64/0.56  % (16271)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.64/0.56  % (16262)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.64/0.56  % (16256)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.64/0.57  % (16267)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.64/0.57  % (16274)Refutation not found, incomplete strategy% (16274)------------------------------
% 1.64/0.57  % (16274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.57  % (16274)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.57  
% 1.64/0.57  % (16274)Memory used [KB]: 10618
% 1.64/0.57  % (16274)Time elapsed: 0.151 s
% 1.64/0.57  % (16274)------------------------------
% 1.64/0.57  % (16274)------------------------------
% 1.64/0.58  % (16265)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.64/0.58  % (16270)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.64/0.59  % (16255)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.64/0.59  % (16255)Refutation not found, incomplete strategy% (16255)------------------------------
% 1.64/0.59  % (16255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (16255)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.59  
% 1.64/0.59  % (16255)Memory used [KB]: 10618
% 1.64/0.59  % (16255)Time elapsed: 0.157 s
% 1.64/0.59  % (16255)------------------------------
% 1.64/0.59  % (16255)------------------------------
% 1.64/0.60  % (16265)Refutation not found, incomplete strategy% (16265)------------------------------
% 1.64/0.60  % (16265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.60  % (16265)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.60  
% 1.64/0.60  % (16265)Memory used [KB]: 10618
% 1.64/0.60  % (16265)Time elapsed: 0.173 s
% 1.64/0.60  % (16265)------------------------------
% 1.64/0.60  % (16265)------------------------------
% 1.64/0.60  % (16273)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 2.32/0.67  % (16266)Refutation found. Thanks to Tanya!
% 2.32/0.67  % SZS status Theorem for theBenchmark
% 2.32/0.67  % SZS output start Proof for theBenchmark
% 2.32/0.67  fof(f2943,plain,(
% 2.32/0.67    $false),
% 2.32/0.67    inference(avatar_sat_refutation,[],[f135,f136,f137,f138,f140,f148,f150,f164,f449,f906,f907,f915,f979,f2856,f2876,f2877,f2942])).
% 2.32/0.67  fof(f2942,plain,(
% 2.32/0.67    ~spl10_163 | ~spl10_83 | spl10_9),
% 2.32/0.67    inference(avatar_split_clause,[],[f2939,f152,f1168,f2870])).
% 2.32/0.67  fof(f2870,plain,(
% 2.32/0.67    spl10_163 <=> r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0))),
% 2.32/0.67    introduced(avatar_definition,[new_symbols(naming,[spl10_163])])).
% 2.32/0.67  fof(f1168,plain,(
% 2.32/0.67    spl10_83 <=> r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))),
% 2.32/0.67    introduced(avatar_definition,[new_symbols(naming,[spl10_83])])).
% 2.32/0.67  fof(f152,plain,(
% 2.32/0.67    spl10_9 <=> r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),
% 2.32/0.67    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 2.32/0.67  fof(f2939,plain,(
% 2.32/0.67    ~r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1)) | ~r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0)) | spl10_9),
% 2.32/0.67    inference(resolution,[],[f153,f66])).
% 2.32/0.67  fof(f66,plain,(
% 2.32/0.67    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.32/0.67    inference(equality_resolution,[],[f56])).
% 2.32/0.67  fof(f56,plain,(
% 2.32/0.67    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 2.32/0.67    inference(cnf_transformation,[],[f34])).
% 2.32/0.67  fof(f34,plain,(
% 2.32/0.67    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.32/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f32,f33])).
% 2.32/0.67  fof(f33,plain,(
% 2.32/0.67    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 2.32/0.67    introduced(choice_axiom,[])).
% 2.32/0.67  fof(f32,plain,(
% 2.32/0.67    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.32/0.67    inference(rectify,[],[f31])).
% 2.32/0.67  fof(f31,plain,(
% 2.32/0.67    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.32/0.67    inference(flattening,[],[f30])).
% 2.32/0.67  fof(f30,plain,(
% 2.32/0.67    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.32/0.67    inference(nnf_transformation,[],[f1])).
% 2.32/0.67  fof(f1,axiom,(
% 2.32/0.67    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.32/0.67  fof(f153,plain,(
% 2.32/0.67    ~r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) | spl10_9),
% 2.32/0.67    inference(avatar_component_clause,[],[f152])).
% 2.32/0.67  fof(f2877,plain,(
% 2.32/0.67    ~spl10_10 | spl10_163 | ~spl10_2 | ~spl10_11),
% 2.32/0.67    inference(avatar_split_clause,[],[f803,f161,f102,f2870,f156])).
% 2.32/0.67  fof(f156,plain,(
% 2.32/0.67    spl10_10 <=> r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2))),
% 2.32/0.67    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 2.32/0.67  fof(f102,plain,(
% 2.32/0.67    spl10_2 <=> ! [X16,X17] : (r2_hidden(X16,k10_relat_1(sK2,X17)) | ~r2_hidden(X16,k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,X16),X17))),
% 2.32/0.67    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 2.32/0.67  fof(f161,plain,(
% 2.32/0.67    spl10_11 <=> r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k3_xboole_0(sK0,sK1))),
% 2.32/0.67    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 2.32/0.67  fof(f803,plain,(
% 2.32/0.67    r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0)) | ~r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2)) | (~spl10_2 | ~spl10_11)),
% 2.32/0.67    inference(resolution,[],[f354,f163])).
% 2.32/0.67  fof(f163,plain,(
% 2.32/0.67    r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k3_xboole_0(sK0,sK1)) | ~spl10_11),
% 2.32/0.67    inference(avatar_component_clause,[],[f161])).
% 2.32/0.67  fof(f354,plain,(
% 2.32/0.67    ( ! [X6,X4,X5] : (~r2_hidden(k1_funct_1(sK2,X4),k3_xboole_0(X5,X6)) | r2_hidden(X4,k10_relat_1(sK2,X5)) | ~r2_hidden(X4,k1_relat_1(sK2))) ) | ~spl10_2),
% 2.32/0.67    inference(resolution,[],[f103,f68])).
% 2.32/0.67  fof(f68,plain,(
% 2.32/0.67    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 2.32/0.67    inference(equality_resolution,[],[f54])).
% 2.32/0.67  fof(f54,plain,(
% 2.32/0.67    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.32/0.67    inference(cnf_transformation,[],[f34])).
% 2.32/0.67  fof(f103,plain,(
% 2.32/0.67    ( ! [X17,X16] : (~r2_hidden(k1_funct_1(sK2,X16),X17) | ~r2_hidden(X16,k1_relat_1(sK2)) | r2_hidden(X16,k10_relat_1(sK2,X17))) ) | ~spl10_2),
% 2.32/0.67    inference(avatar_component_clause,[],[f102])).
% 2.32/0.67  fof(f2876,plain,(
% 2.32/0.67    ~spl10_10 | spl10_83 | ~spl10_2 | ~spl10_11),
% 2.32/0.67    inference(avatar_split_clause,[],[f821,f161,f102,f1168,f156])).
% 2.32/0.67  fof(f821,plain,(
% 2.32/0.67    r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1)) | ~r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2)) | (~spl10_2 | ~spl10_11)),
% 2.32/0.67    inference(resolution,[],[f355,f163])).
% 2.32/0.67  fof(f355,plain,(
% 2.32/0.67    ( ! [X8,X7,X9] : (~r2_hidden(k1_funct_1(sK2,X7),k3_xboole_0(X9,X8)) | r2_hidden(X7,k10_relat_1(sK2,X8)) | ~r2_hidden(X7,k1_relat_1(sK2))) ) | ~spl10_2),
% 2.32/0.67    inference(resolution,[],[f103,f67])).
% 2.32/0.67  fof(f67,plain,(
% 2.32/0.67    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 2.32/0.67    inference(equality_resolution,[],[f55])).
% 2.32/0.67  fof(f55,plain,(
% 2.32/0.67    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.32/0.67    inference(cnf_transformation,[],[f34])).
% 2.32/0.67  fof(f2856,plain,(
% 2.32/0.67    ~spl10_3 | ~spl10_9 | spl10_64),
% 2.32/0.67    inference(avatar_contradiction_clause,[],[f2844])).
% 2.32/0.67  fof(f2844,plain,(
% 2.32/0.67    $false | (~spl10_3 | ~spl10_9 | spl10_64)),
% 2.32/0.67    inference(resolution,[],[f475,f978])).
% 2.32/0.67  fof(f978,plain,(
% 2.32/0.67    ~r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1) | spl10_64),
% 2.32/0.67    inference(avatar_component_clause,[],[f976])).
% 2.32/0.67  fof(f976,plain,(
% 2.32/0.67    spl10_64 <=> r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1)),
% 2.32/0.67    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).
% 2.32/0.67  fof(f475,plain,(
% 2.32/0.67    r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1) | (~spl10_3 | ~spl10_9)),
% 2.32/0.67    inference(resolution,[],[f154,f226])).
% 2.32/0.67  fof(f226,plain,(
% 2.32/0.67    ( ! [X12,X13,X11] : (~r2_hidden(X11,k3_xboole_0(X13,k10_relat_1(sK2,X12))) | r2_hidden(k1_funct_1(sK2,X11),X12)) ) | ~spl10_3),
% 2.32/0.67    inference(resolution,[],[f107,f67])).
% 2.32/0.67  fof(f107,plain,(
% 2.32/0.67    ( ! [X19,X18] : (~r2_hidden(X18,k10_relat_1(sK2,X19)) | r2_hidden(k1_funct_1(sK2,X18),X19)) ) | ~spl10_3),
% 2.32/0.67    inference(avatar_component_clause,[],[f106])).
% 2.32/0.67  fof(f106,plain,(
% 2.32/0.67    spl10_3 <=> ! [X18,X19] : (r2_hidden(k1_funct_1(sK2,X18),X19) | ~r2_hidden(X18,k10_relat_1(sK2,X19)))),
% 2.32/0.67    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 2.32/0.67  fof(f154,plain,(
% 2.32/0.67    r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) | ~spl10_9),
% 2.32/0.67    inference(avatar_component_clause,[],[f152])).
% 2.32/0.67  fof(f979,plain,(
% 2.32/0.67    ~spl10_58 | ~spl10_64 | spl10_11),
% 2.32/0.67    inference(avatar_split_clause,[],[f972,f161,f976,f910])).
% 2.32/0.67  fof(f910,plain,(
% 2.32/0.67    spl10_58 <=> r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0)),
% 2.32/0.67    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).
% 2.32/0.67  fof(f972,plain,(
% 2.32/0.67    ~r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK1) | ~r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0) | spl10_11),
% 2.32/0.67    inference(resolution,[],[f162,f66])).
% 2.32/0.67  fof(f162,plain,(
% 2.32/0.67    ~r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k3_xboole_0(sK0,sK1)) | spl10_11),
% 2.32/0.67    inference(avatar_component_clause,[],[f161])).
% 2.32/0.67  fof(f915,plain,(
% 2.32/0.67    spl10_58 | ~spl10_3 | ~spl10_9),
% 2.32/0.67    inference(avatar_split_clause,[],[f476,f152,f106,f910])).
% 2.32/0.67  fof(f476,plain,(
% 2.32/0.67    r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),sK0) | (~spl10_3 | ~spl10_9)),
% 2.32/0.67    inference(resolution,[],[f154,f225])).
% 2.32/0.67  fof(f225,plain,(
% 2.32/0.67    ( ! [X10,X8,X9] : (~r2_hidden(X8,k3_xboole_0(k10_relat_1(sK2,X9),X10)) | r2_hidden(k1_funct_1(sK2,X8),X9)) ) | ~spl10_3),
% 2.32/0.67    inference(resolution,[],[f107,f68])).
% 2.32/0.67  fof(f907,plain,(
% 2.32/0.67    ~spl10_11 | ~spl10_10 | ~spl10_9 | ~spl10_5),
% 2.32/0.67    inference(avatar_split_clause,[],[f523,f114,f152,f156,f161])).
% 2.32/0.67  fof(f114,plain,(
% 2.32/0.67    spl10_5 <=> ! [X29,X30] : (sQ9_eqProxy(k10_relat_1(sK2,X29),X30) | ~r2_hidden(sK6(sK2,X29,X30),X30) | ~r2_hidden(sK6(sK2,X29,X30),k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,sK6(sK2,X29,X30)),X29))),
% 2.32/0.67    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 2.32/0.67  fof(f523,plain,(
% 2.32/0.67    ~r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) | ~r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k3_xboole_0(sK0,sK1)) | ~spl10_5),
% 2.32/0.67    inference(resolution,[],[f115,f70])).
% 2.32/0.67  fof(f70,plain,(
% 2.32/0.67    ~sQ9_eqProxy(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),
% 2.32/0.67    inference(equality_proxy_replacement,[],[f37,f69])).
% 2.32/0.67  fof(f69,plain,(
% 2.32/0.67    ! [X1,X0] : (sQ9_eqProxy(X0,X1) <=> X0 = X1)),
% 2.32/0.67    introduced(equality_proxy_definition,[new_symbols(naming,[sQ9_eqProxy])])).
% 2.32/0.67  fof(f37,plain,(
% 2.32/0.67    k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 2.32/0.67    inference(cnf_transformation,[],[f14])).
% 2.32/0.67  fof(f14,plain,(
% 2.32/0.67    k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 2.32/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).
% 2.32/0.67  fof(f13,plain,(
% 2.32/0.67    ? [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 2.32/0.67    introduced(choice_axiom,[])).
% 2.32/0.67  fof(f8,plain,(
% 2.32/0.67    ? [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.32/0.67    inference(flattening,[],[f7])).
% 2.32/0.67  fof(f7,plain,(
% 2.32/0.67    ? [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 2.32/0.67    inference(ennf_transformation,[],[f6])).
% 2.32/0.67  fof(f6,negated_conjecture,(
% 2.32/0.67    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 2.32/0.67    inference(negated_conjecture,[],[f5])).
% 2.32/0.67  fof(f5,conjecture,(
% 2.32/0.67    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 2.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).
% 2.32/0.67  fof(f115,plain,(
% 2.32/0.67    ( ! [X30,X29] : (sQ9_eqProxy(k10_relat_1(sK2,X29),X30) | ~r2_hidden(sK6(sK2,X29,X30),X30) | ~r2_hidden(sK6(sK2,X29,X30),k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,sK6(sK2,X29,X30)),X29)) ) | ~spl10_5),
% 2.32/0.67    inference(avatar_component_clause,[],[f114])).
% 2.32/0.67  fof(f906,plain,(
% 2.32/0.67    ~spl10_4 | ~spl10_9 | spl10_10),
% 2.32/0.67    inference(avatar_contradiction_clause,[],[f891])).
% 2.32/0.67  fof(f891,plain,(
% 2.32/0.67    $false | (~spl10_4 | ~spl10_9 | spl10_10)),
% 2.32/0.67    inference(resolution,[],[f477,f451])).
% 2.32/0.67  fof(f451,plain,(
% 2.32/0.67    ( ! [X0] : (~r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,X0))) ) | (~spl10_4 | spl10_10)),
% 2.32/0.67    inference(resolution,[],[f157,f111])).
% 2.32/0.67  fof(f111,plain,(
% 2.32/0.67    ( ! [X21,X20] : (r2_hidden(X20,k1_relat_1(sK2)) | ~r2_hidden(X20,k10_relat_1(sK2,X21))) ) | ~spl10_4),
% 2.32/0.67    inference(avatar_component_clause,[],[f110])).
% 2.32/0.67  fof(f110,plain,(
% 2.32/0.67    spl10_4 <=> ! [X20,X21] : (r2_hidden(X20,k1_relat_1(sK2)) | ~r2_hidden(X20,k10_relat_1(sK2,X21)))),
% 2.32/0.67    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 2.32/0.67  fof(f157,plain,(
% 2.32/0.67    ~r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2)) | spl10_10),
% 2.32/0.67    inference(avatar_component_clause,[],[f156])).
% 2.32/0.67  fof(f477,plain,(
% 2.32/0.67    r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK0)) | ~spl10_9),
% 2.32/0.67    inference(resolution,[],[f154,f68])).
% 2.32/0.67  fof(f449,plain,(
% 2.32/0.67    spl10_10 | spl10_9 | ~spl10_7),
% 2.32/0.67    inference(avatar_split_clause,[],[f427,f122,f152,f156])).
% 2.32/0.67  fof(f122,plain,(
% 2.32/0.67    spl10_7 <=> ! [X34,X33] : (sQ9_eqProxy(k10_relat_1(sK2,X33),X34) | r2_hidden(sK6(sK2,X33,X34),X34) | r2_hidden(sK6(sK2,X33,X34),k1_relat_1(sK2)))),
% 2.32/0.67    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 2.32/0.67  fof(f427,plain,(
% 2.32/0.67    r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) | r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k1_relat_1(sK2)) | ~spl10_7),
% 2.32/0.67    inference(resolution,[],[f123,f70])).
% 2.32/0.67  fof(f123,plain,(
% 2.32/0.67    ( ! [X33,X34] : (sQ9_eqProxy(k10_relat_1(sK2,X33),X34) | r2_hidden(sK6(sK2,X33,X34),X34) | r2_hidden(sK6(sK2,X33,X34),k1_relat_1(sK2))) ) | ~spl10_7),
% 2.32/0.67    inference(avatar_component_clause,[],[f122])).
% 2.32/0.67  fof(f164,plain,(
% 2.32/0.67    ~spl10_8 | ~spl10_1 | spl10_9 | spl10_11),
% 2.32/0.67    inference(avatar_split_clause,[],[f142,f161,f152,f98,f132])).
% 2.32/0.67  fof(f132,plain,(
% 2.32/0.67    spl10_8 <=> v1_relat_1(sK2)),
% 2.32/0.67    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 2.32/0.67  fof(f98,plain,(
% 2.32/0.67    spl10_1 <=> v1_funct_1(sK2)),
% 2.32/0.67    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 2.32/0.67  fof(f142,plain,(
% 2.32/0.67    r2_hidden(k1_funct_1(sK2,sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),k3_xboole_0(sK0,sK1)) | r2_hidden(sK6(sK2,k3_xboole_0(sK0,sK1),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.32/0.67    inference(resolution,[],[f70,f75])).
% 2.32/0.67  fof(f75,plain,(
% 2.32/0.67    ( ! [X2,X0,X1] : (sQ9_eqProxy(k10_relat_1(X0,X1),X2) | r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1) | r2_hidden(sK6(X0,X1,X2),X2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.67    inference(equality_proxy_replacement,[],[f48,f69])).
% 2.32/0.67  fof(f48,plain,(
% 2.32/0.67    ( ! [X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1) | r2_hidden(sK6(X0,X1,X2),X2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.67    inference(cnf_transformation,[],[f25])).
% 2.32/0.67  fof(f25,plain,(
% 2.32/0.67    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((~r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1) | ~r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.32/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f24])).
% 2.32/0.67  fof(f24,plain,(
% 2.32/0.67    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1) | ~r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 2.32/0.67    introduced(choice_axiom,[])).
% 2.32/0.67  fof(f23,plain,(
% 2.32/0.67    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.32/0.67    inference(rectify,[],[f22])).
% 2.32/0.67  fof(f22,plain,(
% 2.32/0.67    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.32/0.67    inference(flattening,[],[f21])).
% 2.32/0.67  fof(f21,plain,(
% 2.32/0.67    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.32/0.67    inference(nnf_transformation,[],[f11])).
% 2.32/0.67  fof(f11,plain,(
% 2.32/0.67    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.32/0.67    inference(flattening,[],[f10])).
% 2.32/0.67  fof(f10,plain,(
% 2.32/0.67    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.32/0.67    inference(ennf_transformation,[],[f4])).
% 2.32/0.67  fof(f4,axiom,(
% 2.32/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.32/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).
% 2.32/0.67  fof(f150,plain,(
% 2.32/0.67    spl10_8),
% 2.32/0.67    inference(avatar_contradiction_clause,[],[f149])).
% 2.32/0.67  fof(f149,plain,(
% 2.32/0.67    $false | spl10_8),
% 2.32/0.67    inference(resolution,[],[f134,f35])).
% 2.32/0.67  fof(f35,plain,(
% 2.32/0.67    v1_relat_1(sK2)),
% 2.32/0.67    inference(cnf_transformation,[],[f14])).
% 2.32/0.67  fof(f134,plain,(
% 2.32/0.67    ~v1_relat_1(sK2) | spl10_8),
% 2.32/0.67    inference(avatar_component_clause,[],[f132])).
% 2.32/0.67  fof(f148,plain,(
% 2.32/0.67    spl10_1),
% 2.32/0.67    inference(avatar_contradiction_clause,[],[f147])).
% 2.32/0.67  fof(f147,plain,(
% 2.32/0.67    $false | spl10_1),
% 2.32/0.67    inference(resolution,[],[f100,f36])).
% 2.32/0.67  fof(f36,plain,(
% 2.32/0.67    v1_funct_1(sK2)),
% 2.32/0.67    inference(cnf_transformation,[],[f14])).
% 2.32/0.67  fof(f100,plain,(
% 2.32/0.67    ~v1_funct_1(sK2) | spl10_1),
% 2.32/0.67    inference(avatar_component_clause,[],[f98])).
% 2.32/0.67  fof(f140,plain,(
% 2.32/0.67    ~spl10_8 | spl10_5),
% 2.32/0.67    inference(avatar_split_clause,[],[f130,f114,f132])).
% 2.32/0.67  fof(f130,plain,(
% 2.32/0.67    ( ! [X10,X11] : (sQ9_eqProxy(k10_relat_1(sK2,X10),X11) | ~r2_hidden(k1_funct_1(sK2,sK6(sK2,X10,X11)),X10) | ~r2_hidden(sK6(sK2,X10,X11),k1_relat_1(sK2)) | ~r2_hidden(sK6(sK2,X10,X11),X11) | ~v1_relat_1(sK2)) )),
% 2.32/0.67    inference(resolution,[],[f36,f74])).
% 2.32/0.67  fof(f74,plain,(
% 2.32/0.67    ( ! [X2,X0,X1] : (sQ9_eqProxy(k10_relat_1(X0,X1),X2) | ~r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1) | ~r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK6(X0,X1,X2),X2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.67    inference(equality_proxy_replacement,[],[f49,f69])).
% 2.32/0.67  fof(f49,plain,(
% 2.32/0.67    ( ! [X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | ~r2_hidden(k1_funct_1(X0,sK6(X0,X1,X2)),X1) | ~r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK6(X0,X1,X2),X2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.67    inference(cnf_transformation,[],[f25])).
% 2.32/0.67  fof(f138,plain,(
% 2.32/0.67    ~spl10_8 | spl10_7),
% 2.32/0.67    inference(avatar_split_clause,[],[f128,f122,f132])).
% 2.32/0.67  fof(f128,plain,(
% 2.32/0.67    ( ! [X6,X7] : (sQ9_eqProxy(k10_relat_1(sK2,X6),X7) | r2_hidden(sK6(sK2,X6,X7),k1_relat_1(sK2)) | r2_hidden(sK6(sK2,X6,X7),X7) | ~v1_relat_1(sK2)) )),
% 2.32/0.67    inference(resolution,[],[f36,f76])).
% 2.32/0.67  fof(f76,plain,(
% 2.32/0.67    ( ! [X2,X0,X1] : (sQ9_eqProxy(k10_relat_1(X0,X1),X2) | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) | r2_hidden(sK6(X0,X1,X2),X2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.67    inference(equality_proxy_replacement,[],[f47,f69])).
% 2.32/0.67  fof(f47,plain,(
% 2.32/0.67    ( ! [X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) | r2_hidden(sK6(X0,X1,X2),X2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.67    inference(cnf_transformation,[],[f25])).
% 2.32/0.67  fof(f137,plain,(
% 2.32/0.67    ~spl10_8 | spl10_2),
% 2.32/0.67    inference(avatar_split_clause,[],[f127,f102,f132])).
% 2.32/0.67  fof(f127,plain,(
% 2.32/0.67    ( ! [X4,X5] : (r2_hidden(X4,k10_relat_1(sK2,X5)) | ~r2_hidden(k1_funct_1(sK2,X4),X5) | ~r2_hidden(X4,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 2.32/0.67    inference(resolution,[],[f36,f63])).
% 2.32/0.67  fof(f63,plain,(
% 2.32/0.67    ( ! [X4,X0,X1] : (r2_hidden(X4,k10_relat_1(X0,X1)) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.67    inference(equality_resolution,[],[f46])).
% 2.32/0.67  fof(f46,plain,(
% 2.32/0.67    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0)) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.67    inference(cnf_transformation,[],[f25])).
% 2.32/0.67  fof(f136,plain,(
% 2.32/0.67    ~spl10_8 | spl10_3),
% 2.32/0.67    inference(avatar_split_clause,[],[f126,f106,f132])).
% 2.32/0.67  fof(f126,plain,(
% 2.32/0.67    ( ! [X2,X3] : (r2_hidden(k1_funct_1(sK2,X2),X3) | ~r2_hidden(X2,k10_relat_1(sK2,X3)) | ~v1_relat_1(sK2)) )),
% 2.32/0.67    inference(resolution,[],[f36,f64])).
% 2.32/0.67  fof(f64,plain,(
% 2.32/0.67    ( ! [X4,X0,X1] : (r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.67    inference(equality_resolution,[],[f45])).
% 2.32/0.67  fof(f45,plain,(
% 2.32/0.67    ( ! [X4,X2,X0,X1] : (r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.67    inference(cnf_transformation,[],[f25])).
% 2.32/0.67  fof(f135,plain,(
% 2.32/0.67    ~spl10_8 | spl10_4),
% 2.32/0.67    inference(avatar_split_clause,[],[f125,f110,f132])).
% 2.32/0.67  fof(f125,plain,(
% 2.32/0.67    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(X0,k10_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 2.32/0.67    inference(resolution,[],[f36,f65])).
% 2.32/0.67  fof(f65,plain,(
% 2.32/0.67    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.67    inference(equality_resolution,[],[f44])).
% 2.32/0.67  fof(f44,plain,(
% 2.32/0.67    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.67    inference(cnf_transformation,[],[f25])).
% 2.32/0.67  % SZS output end Proof for theBenchmark
% 2.32/0.67  % (16266)------------------------------
% 2.32/0.67  % (16266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.32/0.67  % (16266)Termination reason: Refutation
% 2.32/0.67  
% 2.32/0.67  % (16266)Memory used [KB]: 8187
% 2.32/0.67  % (16266)Time elapsed: 0.219 s
% 2.32/0.67  % (16266)------------------------------
% 2.32/0.67  % (16266)------------------------------
% 2.32/0.67  % (16253)Success in time 0.317 s
%------------------------------------------------------------------------------

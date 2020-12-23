%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0470+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:31 EST 2020

% Result     : Theorem 3.46s
% Output     : Refutation 4.24s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 173 expanded)
%              Number of leaves         :   20 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  286 ( 571 expanded)
%              Number of equality atoms :   30 (  94 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6079,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3754,f5950,f5970,f6005,f6033,f6053,f6078])).

fof(f6078,plain,(
    ~ spl144_6 ),
    inference(avatar_contradiction_clause,[],[f6077])).

fof(f6077,plain,
    ( $false
    | ~ spl144_6 ),
    inference(subsumption_resolution,[],[f6070,f1612])).

fof(f1612,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f6070,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl144_6 ),
    inference(resolution,[],[f6064,f1731])).

fof(f1731,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f782])).

fof(f782,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f638])).

fof(f638,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f6064,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl144_6 ),
    inference(subsumption_resolution,[],[f6063,f1609])).

fof(f1609,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f1219])).

fof(f1219,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f720,f1218])).

fof(f1218,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f720,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f703])).

fof(f703,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f702])).

fof(f702,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f6063,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | ~ spl144_6 ),
    inference(subsumption_resolution,[],[f6059,f3765])).

fof(f3765,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f1749,f1612])).

fof(f1749,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f1256])).

fof(f1256,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK23(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f1254,f1255])).

fof(f1255,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK23(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1254,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f1253])).

fof(f1253,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f6059,plain,
    ( r2_hidden(k4_tarski(sK17(sK3,k1_xboole_0,sK8(k5_relat_1(sK3,k1_xboole_0)),sK9(k5_relat_1(sK3,k1_xboole_0))),sK9(k5_relat_1(sK3,k1_xboole_0))),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | ~ spl144_6 ),
    inference(resolution,[],[f6032,f3780])).

fof(f3780,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK17(X0,X1,X7,X8),X8),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f2721,f2035])).

fof(f2035,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f982])).

fof(f982,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f981])).

fof(f981,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f652])).

fof(f652,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f2721,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK17(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1721])).

fof(f1721,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK17(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1243])).

fof(f1243,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK15(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK14(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK14(X0,X1,X2),sK15(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK16(X0,X1,X2),sK15(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK14(X0,X1,X2),sK16(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK14(X0,X1,X2),sK15(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK17(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK17(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16,sK17])],[f1239,f1242,f1241,f1240])).

fof(f1240,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK15(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK14(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK14(X0,X1,X2),sK15(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK15(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK14(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK14(X0,X1,X2),sK15(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1241,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK15(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK14(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK16(X0,X1,X2),sK15(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK14(X0,X1,X2),sK16(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1242,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK17(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK17(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1239,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1238])).

fof(f1238,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f777])).

fof(f777,plain,(
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
    inference(ennf_transformation,[],[f647])).

fof(f647,axiom,(
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

fof(f6032,plain,
    ( r2_hidden(k4_tarski(sK8(k5_relat_1(sK3,k1_xboole_0)),sK9(k5_relat_1(sK3,k1_xboole_0))),k5_relat_1(sK3,k1_xboole_0))
    | ~ spl144_6 ),
    inference(avatar_component_clause,[],[f6030])).

fof(f6030,plain,
    ( spl144_6
  <=> r2_hidden(k4_tarski(sK8(k5_relat_1(sK3,k1_xboole_0)),sK9(k5_relat_1(sK3,k1_xboole_0))),k5_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl144_6])])).

fof(f6053,plain,(
    spl144_5 ),
    inference(avatar_contradiction_clause,[],[f6052])).

fof(f6052,plain,
    ( $false
    | spl144_5 ),
    inference(subsumption_resolution,[],[f6045,f1612])).

fof(f6045,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl144_5 ),
    inference(resolution,[],[f6038,f1731])).

fof(f6038,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl144_5 ),
    inference(subsumption_resolution,[],[f6034,f1609])).

fof(f6034,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | spl144_5 ),
    inference(resolution,[],[f6028,f2035])).

fof(f6028,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | spl144_5 ),
    inference(avatar_component_clause,[],[f6026])).

fof(f6026,plain,
    ( spl144_5
  <=> v1_relat_1(k5_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl144_5])])).

fof(f6033,plain,
    ( ~ spl144_5
    | spl144_6
    | spl144_2 ),
    inference(avatar_split_clause,[],[f4760,f3751,f6030,f6026])).

fof(f3751,plain,
    ( spl144_2
  <=> sQ143_eqProxy(k1_xboole_0,k5_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl144_2])])).

fof(f4760,plain,
    ( r2_hidden(k4_tarski(sK8(k5_relat_1(sK3,k1_xboole_0)),sK9(k5_relat_1(sK3,k1_xboole_0))),k5_relat_1(sK3,k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | spl144_2 ),
    inference(resolution,[],[f2960,f3753])).

fof(f3753,plain,
    ( ~ sQ143_eqProxy(k1_xboole_0,k5_relat_1(sK3,k1_xboole_0))
    | spl144_2 ),
    inference(avatar_component_clause,[],[f3751])).

fof(f2960,plain,(
    ! [X0] :
      ( sQ143_eqProxy(k1_xboole_0,X0)
      | r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f1686,f2912])).

fof(f2912,plain,(
    ! [X1,X0] :
      ( sQ143_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ143_eqProxy])])).

fof(f1686,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1229])).

fof(f1229,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f744,f1228])).

fof(f1228,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f744,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f743])).

fof(f743,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f700])).

fof(f700,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(f6005,plain,(
    ~ spl144_4 ),
    inference(avatar_contradiction_clause,[],[f6004])).

fof(f6004,plain,
    ( $false
    | ~ spl144_4 ),
    inference(subsumption_resolution,[],[f5997,f1612])).

fof(f5997,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl144_4 ),
    inference(resolution,[],[f5990,f1731])).

fof(f5990,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl144_4 ),
    inference(subsumption_resolution,[],[f5989,f1609])).

fof(f5989,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl144_4 ),
    inference(subsumption_resolution,[],[f5985,f3765])).

fof(f5985,plain,
    ( r2_hidden(k4_tarski(sK8(k5_relat_1(k1_xboole_0,sK3)),sK17(k1_xboole_0,sK3,sK8(k5_relat_1(k1_xboole_0,sK3)),sK9(k5_relat_1(k1_xboole_0,sK3)))),k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl144_4 ),
    inference(resolution,[],[f5949,f3781])).

fof(f3781,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X7,sK17(X0,X1,X7,X8)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f2722,f2035])).

fof(f2722,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK17(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1720])).

fof(f1720,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK17(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1243])).

fof(f5949,plain,
    ( r2_hidden(k4_tarski(sK8(k5_relat_1(k1_xboole_0,sK3)),sK9(k5_relat_1(k1_xboole_0,sK3))),k5_relat_1(k1_xboole_0,sK3))
    | ~ spl144_4 ),
    inference(avatar_component_clause,[],[f5947])).

fof(f5947,plain,
    ( spl144_4
  <=> r2_hidden(k4_tarski(sK8(k5_relat_1(k1_xboole_0,sK3)),sK9(k5_relat_1(k1_xboole_0,sK3))),k5_relat_1(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl144_4])])).

fof(f5970,plain,(
    spl144_3 ),
    inference(avatar_contradiction_clause,[],[f5969])).

fof(f5969,plain,
    ( $false
    | spl144_3 ),
    inference(subsumption_resolution,[],[f5962,f1612])).

fof(f5962,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl144_3 ),
    inference(resolution,[],[f5955,f1731])).

fof(f5955,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl144_3 ),
    inference(subsumption_resolution,[],[f5951,f1609])).

fof(f5951,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k1_xboole_0)
    | spl144_3 ),
    inference(resolution,[],[f5945,f2035])).

fof(f5945,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK3))
    | spl144_3 ),
    inference(avatar_component_clause,[],[f5943])).

fof(f5943,plain,
    ( spl144_3
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl144_3])])).

fof(f5950,plain,
    ( ~ spl144_3
    | spl144_4
    | spl144_1 ),
    inference(avatar_split_clause,[],[f4759,f3747,f5947,f5943])).

fof(f3747,plain,
    ( spl144_1
  <=> sQ143_eqProxy(k1_xboole_0,k5_relat_1(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl144_1])])).

fof(f4759,plain,
    ( r2_hidden(k4_tarski(sK8(k5_relat_1(k1_xboole_0,sK3)),sK9(k5_relat_1(k1_xboole_0,sK3))),k5_relat_1(k1_xboole_0,sK3))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK3))
    | spl144_1 ),
    inference(resolution,[],[f2960,f3749])).

fof(f3749,plain,
    ( ~ sQ143_eqProxy(k1_xboole_0,k5_relat_1(k1_xboole_0,sK3))
    | spl144_1 ),
    inference(avatar_component_clause,[],[f3747])).

fof(f3754,plain,
    ( ~ spl144_1
    | ~ spl144_2 ),
    inference(avatar_split_clause,[],[f2930,f3751,f3747])).

fof(f2930,plain,
    ( ~ sQ143_eqProxy(k1_xboole_0,k5_relat_1(sK3,k1_xboole_0))
    | ~ sQ143_eqProxy(k1_xboole_0,k5_relat_1(k1_xboole_0,sK3)) ),
    inference(equality_proxy_replacement,[],[f1610,f2912,f2912])).

fof(f1610,plain,
    ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f1219])).
%------------------------------------------------------------------------------

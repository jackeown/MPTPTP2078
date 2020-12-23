%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t35_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:26 EDT 2019

% Result     : Theorem 23.29s
% Output     : Refutation 23.29s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 196 expanded)
%              Number of leaves         :   19 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  281 ( 557 expanded)
%              Number of equality atoms :   12 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12975,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f183,f454,f604,f612,f12551,f12859,f12967,f12974])).

fof(f12974,plain,
    ( spl11_11
    | ~ spl11_26
    | spl11_237 ),
    inference(avatar_contradiction_clause,[],[f12973])).

fof(f12973,plain,
    ( $false
    | ~ spl11_11
    | ~ spl11_26
    | ~ spl11_237 ),
    inference(subsumption_resolution,[],[f12858,f12928])).

fof(f12928,plain,
    ( v3_ordinal1(sK2(k3_tarski(sK0)))
    | ~ spl11_11
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f12893,f12558])).

fof(f12558,plain,
    ( r2_hidden(sK2(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl11_11 ),
    inference(resolution,[],[f176,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t35_ordinal1.p',d3_ordinal1)).

fof(f176,plain,
    ( ~ v2_ordinal1(k3_tarski(sK0))
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl11_11
  <=> ~ v2_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f12893,plain,
    ( v3_ordinal1(sK2(k3_tarski(sK0)))
    | ~ r2_hidden(sK2(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl11_26 ),
    inference(resolution,[],[f12571,f86])).

fof(f86,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK7(X0,X2))
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK7(X0,X2))
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t35_ordinal1.p',d4_tarski)).

fof(f12571,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK7(sK0,sK2(k3_tarski(sK0))))
        | v3_ordinal1(X0) )
    | ~ spl11_26 ),
    inference(resolution,[],[f603,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t35_ordinal1.p',t23_ordinal1)).

fof(f603,plain,
    ( v3_ordinal1(sK7(sK0,sK2(k3_tarski(sK0))))
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f602])).

fof(f602,plain,
    ( spl11_26
  <=> v3_ordinal1(sK7(sK0,sK2(k3_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f12858,plain,
    ( ~ v3_ordinal1(sK2(k3_tarski(sK0)))
    | ~ spl11_237 ),
    inference(avatar_component_clause,[],[f12857])).

fof(f12857,plain,
    ( spl11_237
  <=> ~ v3_ordinal1(sK2(k3_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_237])])).

fof(f12967,plain,
    ( spl11_11
    | ~ spl11_28
    | spl11_235 ),
    inference(avatar_contradiction_clause,[],[f12966])).

fof(f12966,plain,
    ( $false
    | ~ spl11_11
    | ~ spl11_28
    | ~ spl11_235 ),
    inference(subsumption_resolution,[],[f12965,f12559])).

fof(f12559,plain,
    ( r2_hidden(sK3(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl11_11 ),
    inference(resolution,[],[f176,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12965,plain,
    ( ~ r2_hidden(sK3(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl11_28
    | ~ spl11_235 ),
    inference(subsumption_resolution,[],[f12930,f12852])).

fof(f12852,plain,
    ( ~ v3_ordinal1(sK3(k3_tarski(sK0)))
    | ~ spl11_235 ),
    inference(avatar_component_clause,[],[f12851])).

fof(f12851,plain,
    ( spl11_235
  <=> ~ v3_ordinal1(sK3(k3_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_235])])).

fof(f12930,plain,
    ( v3_ordinal1(sK3(k3_tarski(sK0)))
    | ~ r2_hidden(sK3(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl11_28 ),
    inference(resolution,[],[f12578,f86])).

fof(f12578,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK7(sK0,sK3(k3_tarski(sK0))))
        | v3_ordinal1(X0) )
    | ~ spl11_28 ),
    inference(resolution,[],[f611,f65])).

fof(f611,plain,
    ( v3_ordinal1(sK7(sK0,sK3(k3_tarski(sK0))))
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f610])).

fof(f610,plain,
    ( spl11_28
  <=> v3_ordinal1(sK7(sK0,sK3(k3_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f12859,plain,
    ( ~ spl11_235
    | ~ spl11_237
    | spl11_11 ),
    inference(avatar_split_clause,[],[f12655,f175,f12857,f12851])).

fof(f12655,plain,
    ( ~ v3_ordinal1(sK2(k3_tarski(sK0)))
    | ~ v3_ordinal1(sK3(k3_tarski(sK0)))
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f12654,f12561])).

fof(f12561,plain,
    ( ~ r2_hidden(sK3(k3_tarski(sK0)),sK2(k3_tarski(sK0)))
    | ~ spl11_11 ),
    inference(resolution,[],[f176,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),sK2(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12654,plain,
    ( ~ v3_ordinal1(sK2(k3_tarski(sK0)))
    | ~ v3_ordinal1(sK3(k3_tarski(sK0)))
    | r2_hidden(sK3(k3_tarski(sK0)),sK2(k3_tarski(sK0)))
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f12649,f12563])).

fof(f12563,plain,
    ( ~ sQ10_eqProxy(sK2(k3_tarski(sK0)),sK3(k3_tarski(sK0)))
    | ~ spl11_11 ),
    inference(resolution,[],[f176,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ sQ10_eqProxy(sK2(X0),sK3(X0))
      | v2_ordinal1(X0) ) ),
    inference(equality_proxy_replacement,[],[f59,f89])).

fof(f89,plain,(
    ! [X1,X0] :
      ( sQ10_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ10_eqProxy])])).

fof(f59,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12649,plain,
    ( ~ v3_ordinal1(sK2(k3_tarski(sK0)))
    | ~ v3_ordinal1(sK3(k3_tarski(sK0)))
    | sQ10_eqProxy(sK2(k3_tarski(sK0)),sK3(k3_tarski(sK0)))
    | r2_hidden(sK3(k3_tarski(sK0)),sK2(k3_tarski(sK0)))
    | ~ spl11_11 ),
    inference(resolution,[],[f12560,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | sQ10_eqProxy(X0,X1)
      | r2_hidden(X1,X0) ) ),
    inference(equality_proxy_replacement,[],[f51,f89])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t35_ordinal1.p',t24_ordinal1)).

fof(f12560,plain,
    ( ~ r2_hidden(sK2(k3_tarski(sK0)),sK3(k3_tarski(sK0)))
    | ~ spl11_11 ),
    inference(resolution,[],[f176,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0),sK3(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12551,plain,
    ( spl11_13
    | ~ spl11_20 ),
    inference(avatar_contradiction_clause,[],[f12550])).

fof(f12550,plain,
    ( $false
    | ~ spl11_13
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f12549,f593])).

fof(f593,plain,
    ( ~ r2_hidden(sK5(sK1(k3_tarski(sK0)),k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl11_13 ),
    inference(resolution,[],[f559,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t35_ordinal1.p',d3_tarski)).

fof(f559,plain,
    ( ~ r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl11_13 ),
    inference(resolution,[],[f182,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t35_ordinal1.p',d2_ordinal1)).

fof(f182,plain,
    ( ~ v1_ordinal1(k3_tarski(sK0))
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl11_13
  <=> ~ v1_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f12549,plain,
    ( r2_hidden(sK5(sK1(k3_tarski(sK0)),k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl11_13
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f12527,f1280])).

fof(f1280,plain,
    ( r1_tarski(sK1(k3_tarski(sK0)),sK7(sK0,sK1(k3_tarski(sK0))))
    | ~ spl11_13
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f1265,f455])).

fof(f455,plain,
    ( v1_ordinal1(sK7(sK0,sK1(k3_tarski(sK0))))
    | ~ spl11_20 ),
    inference(resolution,[],[f453,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t35_ordinal1.p',cc1_ordinal1)).

fof(f453,plain,
    ( v3_ordinal1(sK7(sK0,sK1(k3_tarski(sK0))))
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f452])).

fof(f452,plain,
    ( spl11_20
  <=> v3_ordinal1(sK7(sK0,sK1(k3_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f1265,plain,
    ( r1_tarski(sK1(k3_tarski(sK0)),sK7(sK0,sK1(k3_tarski(sK0))))
    | ~ v1_ordinal1(sK7(sK0,sK1(k3_tarski(sK0))))
    | ~ spl11_13 ),
    inference(resolution,[],[f568,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_tarski(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f568,plain,
    ( r2_hidden(sK1(k3_tarski(sK0)),sK7(sK0,sK1(k3_tarski(sK0))))
    | ~ spl11_13 ),
    inference(resolution,[],[f558,f86])).

fof(f558,plain,
    ( r2_hidden(sK1(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl11_13 ),
    inference(resolution,[],[f182,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12527,plain,
    ( ~ r1_tarski(sK1(k3_tarski(sK0)),sK7(sK0,sK1(k3_tarski(sK0))))
    | r2_hidden(sK5(sK1(k3_tarski(sK0)),k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl11_13 ),
    inference(resolution,[],[f1535,f1102])).

fof(f1102,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK7(sK0,sK1(k3_tarski(sK0))))
        | r2_hidden(X4,k3_tarski(sK0)) )
    | ~ spl11_13 ),
    inference(resolution,[],[f569,f84])).

fof(f84,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f569,plain,
    ( r2_hidden(sK7(sK0,sK1(k3_tarski(sK0))),sK0)
    | ~ spl11_13 ),
    inference(resolution,[],[f558,f85])).

fof(f85,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK7(X0,X2),X0)
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X2),X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1535,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK1(k3_tarski(sK0)),k3_tarski(sK0)),X0)
        | ~ r1_tarski(sK1(k3_tarski(sK0)),X0) )
    | ~ spl11_13 ),
    inference(resolution,[],[f592,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f592,plain,
    ( r2_hidden(sK5(sK1(k3_tarski(sK0)),k3_tarski(sK0)),sK1(k3_tarski(sK0)))
    | ~ spl11_13 ),
    inference(resolution,[],[f559,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f612,plain,
    ( spl11_10
    | spl11_28 ),
    inference(avatar_split_clause,[],[f242,f610,f172])).

fof(f172,plain,
    ( spl11_10
  <=> v2_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f242,plain,
    ( v3_ordinal1(sK7(sK0,sK3(k3_tarski(sK0))))
    | v2_ordinal1(k3_tarski(sK0)) ),
    inference(resolution,[],[f115,f57])).

fof(f115,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,k3_tarski(sK0))
      | v3_ordinal1(sK7(sK0,X12)) ) ),
    inference(resolution,[],[f45,f85])).

fof(f45,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(k3_tarski(X0))
      & ! [X1] :
          ( v3_ordinal1(X1)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v3_ordinal1(X1) )
       => v3_ordinal1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t35_ordinal1.p',t35_ordinal1)).

fof(f604,plain,
    ( spl11_10
    | spl11_26 ),
    inference(avatar_split_clause,[],[f241,f602,f172])).

fof(f241,plain,
    ( v3_ordinal1(sK7(sK0,sK2(k3_tarski(sK0))))
    | v2_ordinal1(k3_tarski(sK0)) ),
    inference(resolution,[],[f115,f56])).

fof(f454,plain,
    ( spl11_12
    | spl11_20 ),
    inference(avatar_split_clause,[],[f240,f452,f178])).

fof(f178,plain,
    ( spl11_12
  <=> v1_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f240,plain,
    ( v3_ordinal1(sK7(sK0,sK1(k3_tarski(sK0))))
    | v1_ordinal1(k3_tarski(sK0)) ),
    inference(resolution,[],[f115,f53])).

fof(f183,plain,
    ( ~ spl11_11
    | ~ spl11_13 ),
    inference(avatar_split_clause,[],[f102,f181,f175])).

fof(f102,plain,
    ( ~ v1_ordinal1(k3_tarski(sK0))
    | ~ v2_ordinal1(k3_tarski(sK0)) ),
    inference(resolution,[],[f46,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
    <=> ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t35_ordinal1.p',d4_ordinal1)).

fof(f46,plain,(
    ~ v3_ordinal1(k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------

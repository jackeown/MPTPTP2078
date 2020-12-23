%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t149_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:16 EDT 2019

% Result     : Theorem 6.94s
% Output     : Refutation 6.94s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 211 expanded)
%              Number of leaves         :   13 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  239 ( 623 expanded)
%              Number of equality atoms :   27 (  68 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9326,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f142,f240,f2432,f3206,f3702,f7520,f9320])).

fof(f9320,plain,
    ( ~ spl10_34
    | spl10_39 ),
    inference(avatar_contradiction_clause,[],[f9316])).

fof(f9316,plain,
    ( $false
    | ~ spl10_34
    | ~ spl10_39 ),
    inference(unit_resulting_resolution,[],[f3701,f131,f893,f3124,f3205])).

fof(f3205,plain,
    ( ! [X12,X10,X11] :
        ( ~ r2_hidden(sK5(sK2,X10,X11),k1_relat_1(sK2))
        | ~ r2_hidden(X11,k9_relat_1(sK2,X10))
        | ~ r2_hidden(sK5(sK2,X10,X11),X12)
        | r2_hidden(X11,k9_relat_1(sK2,X12)) )
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f3204])).

fof(f3204,plain,
    ( spl10_34
  <=> ! [X11,X10,X12] :
        ( r2_hidden(X11,k9_relat_1(sK2,X12))
        | ~ r2_hidden(X11,k9_relat_1(sK2,X10))
        | ~ r2_hidden(sK5(sK2,X10,X11),X12)
        | ~ r2_hidden(sK5(sK2,X10,X11),k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f3124,plain,(
    r2_hidden(sK5(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),sK3(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0)))),sK0) ),
    inference(unit_resulting_resolution,[],[f894,f91])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t149_funct_1.p',d4_xboole_0)).

fof(f894,plain,(
    r2_hidden(sK5(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),sK3(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0)))),k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) ),
    inference(unit_resulting_resolution,[],[f47,f46,f131,f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t149_funct_1.p',d12_funct_1)).

fof(f46,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t149_funct_1.p',t149_funct_1)).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f893,plain,(
    r2_hidden(sK5(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),sK3(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0)))),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f47,f46,f131,f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X1,X3),k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f131,plain,(
    r2_hidden(sK3(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))),k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))) ),
    inference(unit_resulting_resolution,[],[f95,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t149_funct_1.p',d3_tarski)).

fof(f95,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))) ),
    inference(forward_demodulation,[],[f48,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t149_funct_1.p',commutativity_k3_xboole_0)).

fof(f48,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f3701,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))),k9_relat_1(sK2,sK0))
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f3700])).

fof(f3700,plain,
    ( spl10_39
  <=> ~ r2_hidden(sK3(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f7520,plain,
    ( ~ spl10_4
    | ~ spl10_10
    | spl10_37 ),
    inference(avatar_contradiction_clause,[],[f7510])).

fof(f7510,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_37 ),
    inference(unit_resulting_resolution,[],[f131,f894,f3695,f1539])).

fof(f1539,plain,
    ( ! [X6,X8,X7,X9] :
        ( ~ r2_hidden(sK5(sK2,X8,X6),k3_xboole_0(X9,k10_relat_1(sK2,X7)))
        | ~ r2_hidden(X6,k9_relat_1(sK2,X8))
        | r2_hidden(X6,X7) )
    | ~ spl10_4
    | ~ spl10_10 ),
    inference(resolution,[],[f298,f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f298,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(sK5(sK2,X3,X4),k10_relat_1(sK2,X5))
        | r2_hidden(X4,X5)
        | ~ r2_hidden(X4,k9_relat_1(sK2,X3)) )
    | ~ spl10_4
    | ~ spl10_10 ),
    inference(superposition,[],[f141,f239])).

fof(f239,plain,
    ( ! [X8,X9] :
        ( k1_funct_1(sK2,sK5(sK2,X8,X9)) = X9
        | ~ r2_hidden(X9,k9_relat_1(sK2,X8)) )
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl10_10
  <=> ! [X9,X8] :
        ( k1_funct_1(sK2,sK5(sK2,X8,X9)) = X9
        | ~ r2_hidden(X9,k9_relat_1(sK2,X8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f141,plain,
    ( ! [X14,X15] :
        ( r2_hidden(k1_funct_1(sK2,X14),X15)
        | ~ r2_hidden(X14,k10_relat_1(sK2,X15)) )
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl10_4
  <=> ! [X15,X14] :
        ( r2_hidden(k1_funct_1(sK2,X14),X15)
        | ~ r2_hidden(X14,k10_relat_1(sK2,X15)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f3695,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))),sK1)
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f3694])).

fof(f3694,plain,
    ( spl10_37
  <=> ~ r2_hidden(sK3(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f3702,plain,
    ( ~ spl10_37
    | ~ spl10_39 ),
    inference(avatar_split_clause,[],[f626,f3700,f3694])).

fof(f626,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))),k9_relat_1(sK2,sK0))
    | ~ r2_hidden(sK3(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))),sK1) ),
    inference(resolution,[],[f132,f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f132,plain,(
    ~ r2_hidden(sK3(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))) ),
    inference(unit_resulting_resolution,[],[f95,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3206,plain,
    ( ~ spl10_3
    | ~ spl10_27
    | spl10_34
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f300,f238,f3204,f2423,f112])).

fof(f112,plain,
    ( spl10_3
  <=> ~ v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f2423,plain,
    ( spl10_27
  <=> ~ v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f300,plain,
    ( ! [X12,X10,X11] :
        ( r2_hidden(X11,k9_relat_1(sK2,X12))
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(sK5(sK2,X10,X11),k1_relat_1(sK2))
        | ~ r2_hidden(sK5(sK2,X10,X11),X12)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X11,k9_relat_1(sK2,X10)) )
    | ~ spl10_10 ),
    inference(superposition,[],[f85,f239])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | r2_hidden(k1_funct_1(X0,X4),X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | k1_funct_1(X0,X4) != X3
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2432,plain,(
    spl10_27 ),
    inference(avatar_contradiction_clause,[],[f2429])).

fof(f2429,plain,
    ( $false
    | ~ spl10_27 ),
    inference(unit_resulting_resolution,[],[f47,f2424])).

fof(f2424,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f2423])).

fof(f240,plain,
    ( spl10_10
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f100,f112,f238])).

fof(f100,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,sK5(sK2,X8,X9)) = X9
      | ~ r2_hidden(X9,k9_relat_1(sK2,X8)) ) ),
    inference(resolution,[],[f47,f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK5(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK5(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f142,plain,
    ( spl10_4
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f103,f112,f140])).

fof(f103,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(sK2)
      | r2_hidden(k1_funct_1(sK2,X14),X15)
      | ~ r2_hidden(X14,k10_relat_1(sK2,X15)) ) ),
    inference(resolution,[],[f47,f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t149_funct_1.p',d13_funct_1)).

fof(f118,plain,(
    spl10_3 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f46,f113])).

fof(f113,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f112])).
%------------------------------------------------------------------------------

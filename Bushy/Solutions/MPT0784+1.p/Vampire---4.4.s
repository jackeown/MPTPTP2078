%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t33_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:13 EDT 2019

% Result     : Theorem 6.63s
% Output     : Refutation 6.63s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 436 expanded)
%              Number of leaves         :   26 ( 108 expanded)
%              Depth                    :   15
%              Number of atoms          :  394 (1224 expanded)
%              Number of equality atoms :   52 ( 114 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6665,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f350,f365,f440,f458,f3396,f4413,f5270,f5728,f6178,f6664])).

fof(f6664,plain,(
    ~ spl13_52 ),
    inference(avatar_contradiction_clause,[],[f6658])).

fof(f6658,plain,
    ( $false
    | ~ spl13_52 ),
    inference(unit_resulting_resolution,[],[f69,f6179,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      | r3_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X1,X0)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
     => r3_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t33_wellord1.p',symmetry_r3_xboole_0)).

fof(f6179,plain,
    ( ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | ~ spl13_52 ),
    inference(backward_demodulation,[],[f3395,f64])).

fof(f64,plain,(
    ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ~ r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ~ r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( v2_wellord1(X2)
         => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t33_wellord1.p',t33_wellord1)).

fof(f3395,plain,
    ( sK0 = sK1
    | ~ spl13_52 ),
    inference(avatar_component_clause,[],[f3394])).

fof(f3394,plain,
    ( spl13_52
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_52])])).

fof(f69,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(rectify,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : r3_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t33_wellord1.p',reflexivity_r3_xboole_0)).

fof(f6178,plain,(
    ~ spl13_48 ),
    inference(avatar_contradiction_clause,[],[f6174])).

fof(f6174,plain,
    ( $false
    | ~ spl13_48 ),
    inference(unit_resulting_resolution,[],[f142,f112,f5747,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t33_wellord1.p',t2_subset)).

fof(f5747,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl13_48 ),
    inference(backward_demodulation,[],[f3383,f544])).

fof(f544,plain,(
    ~ v1_xboole_0(k1_wellord1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f192,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t33_wellord1.p',t7_boole)).

fof(f192,plain,(
    r2_hidden(sK4(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f141,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox2/benchmark/wellord1__t33_wellord1.p',d3_tarski)).

fof(f141,plain,(
    ~ r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f64,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t33_wellord1.p',d9_xboole_0)).

fof(f3383,plain,
    ( k1_wellord1(sK2,sK1) = k1_xboole_0
    | ~ spl13_48 ),
    inference(avatar_component_clause,[],[f3382])).

fof(f3382,plain,
    ( spl13_48
  <=> k1_wellord1(sK2,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_48])])).

fof(f112,plain,(
    ! [X0] : m1_subset_1(sK12(X0),X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t33_wellord1.p',existence_m1_subset_1)).

fof(f142,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f88,f119,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f119,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_wellord1(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f62,f118])).

fof(f118,plain,(
    ! [X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k1_wellord1(X0,X3)) ) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | X1 != X3
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox2/benchmark/wellord1__t33_wellord1.p',d1_wellord1)).

fof(f62,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t33_wellord1.p',t2_xboole_1)).

fof(f5728,plain,(
    ~ spl13_50 ),
    inference(avatar_contradiction_clause,[],[f5724])).

fof(f5724,plain,
    ( $false
    | ~ spl13_50 ),
    inference(unit_resulting_resolution,[],[f142,f112,f5286,f93])).

fof(f5286,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl13_50 ),
    inference(backward_demodulation,[],[f3389,f303])).

fof(f303,plain,(
    ~ v1_xboole_0(k1_wellord1(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f189,f92])).

fof(f189,plain,(
    r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f140,f86])).

fof(f140,plain,(
    ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f64,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3389,plain,
    ( k1_wellord1(sK2,sK0) = k1_xboole_0
    | ~ spl13_50 ),
    inference(avatar_component_clause,[],[f3388])).

fof(f3388,plain,
    ( spl13_50
  <=> k1_wellord1(sK2,sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_50])])).

fof(f5270,plain,
    ( ~ spl13_10
    | spl13_45
    | ~ spl13_46 ),
    inference(avatar_contradiction_clause,[],[f5255])).

fof(f5255,plain,
    ( $false
    | ~ spl13_10
    | ~ spl13_45
    | ~ spl13_46 ),
    inference(unit_resulting_resolution,[],[f3222,f5146,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t33_wellord1.p',t1_subset)).

fof(f5146,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl13_10
    | ~ spl13_46 ),
    inference(backward_demodulation,[],[f5141,f189])).

fof(f5141,plain,
    ( sK1 = sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl13_10
    | ~ spl13_46 ),
    inference(unit_resulting_resolution,[],[f5048,f140,f190,f900])).

fof(f900,plain,
    ( ! [X8,X7,X9] :
        ( r2_hidden(sK4(k1_wellord1(sK2,X7),X8),k1_wellord1(sK2,X9))
        | ~ r2_hidden(k4_tarski(X7,X9),sK2)
        | sK4(k1_wellord1(sK2,X7),X8) = X9
        | r1_tarski(k1_wellord1(sK2,X7),X8) )
    | ~ spl13_10 ),
    inference(resolution,[],[f644,f127])).

fof(f127,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(k4_tarski(X15,X14),sK2)
      | X14 = X15
      | r2_hidden(X15,k1_wellord1(sK2,X14)) ) ),
    inference(resolution,[],[f62,f115])).

fof(f115,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | X1 = X3
      | ~ r2_hidden(k4_tarski(X3,X1),X0)
      | r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | X1 = X3
      | ~ r2_hidden(k4_tarski(X3,X1),X0)
      | r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f644,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(sK4(k1_wellord1(sK2,X0),X1),X2),sK2)
        | r1_tarski(k1_wellord1(sK2,X0),X1)
        | ~ r2_hidden(k4_tarski(X0,X2),sK2) )
    | ~ spl13_10 ),
    inference(resolution,[],[f245,f349])).

fof(f349,plain,
    ( ! [X10,X11,X9] :
        ( ~ r2_hidden(k4_tarski(X9,X10),sK2)
        | r2_hidden(k4_tarski(X9,X11),sK2)
        | ~ r2_hidden(k4_tarski(X10,X11),sK2) )
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl13_10
  <=> ! [X9,X11,X10] :
        ( ~ r2_hidden(k4_tarski(X9,X10),sK2)
        | r2_hidden(k4_tarski(X9,X11),sK2)
        | ~ r2_hidden(k4_tarski(X10,X11),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f245,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(k1_wellord1(sK2,X0),X1),X0),sK2)
      | r1_tarski(k1_wellord1(sK2,X0),X1) ) ),
    inference(resolution,[],[f128,f86])).

fof(f128,plain,(
    ! [X17,X16] :
      ( ~ r2_hidden(X16,k1_wellord1(sK2,X17))
      | r2_hidden(k4_tarski(X16,X17),sK2) ) ),
    inference(resolution,[],[f62,f116])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f190,plain,(
    ~ r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f140,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5048,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl13_46 ),
    inference(unit_resulting_resolution,[],[f62,f3377,f116])).

fof(f3377,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl13_46 ),
    inference(avatar_component_clause,[],[f3376])).

fof(f3376,plain,
    ( spl13_46
  <=> r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_46])])).

fof(f3222,plain,
    ( ~ m1_subset_1(sK1,k1_wellord1(sK2,sK0))
    | ~ spl13_45 ),
    inference(unit_resulting_resolution,[],[f303,f3216,f93])).

fof(f3216,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl13_45 ),
    inference(unit_resulting_resolution,[],[f62,f3195,f116])).

fof(f3195,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl13_45 ),
    inference(avatar_component_clause,[],[f3194])).

fof(f3194,plain,
    ( spl13_45
  <=> ~ r2_hidden(k4_tarski(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_45])])).

fof(f4413,plain,
    ( ~ spl13_10
    | ~ spl13_44 ),
    inference(avatar_contradiction_clause,[],[f4407])).

fof(f4407,plain,
    ( $false
    | ~ spl13_10
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f69,f3725,f68])).

fof(f3725,plain,
    ( ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | ~ spl13_10
    | ~ spl13_44 ),
    inference(backward_demodulation,[],[f3690,f64])).

fof(f3690,plain,
    ( sK0 = sK1
    | ~ spl13_10
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f133,f62,f3192,f3480,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(k4_tarski(X2,X1),X0)
      | X1 = X2
      | ~ v4_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t33_wellord1.p',l3_wellord1)).

fof(f3480,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl13_10
    | ~ spl13_44 ),
    inference(backward_demodulation,[],[f3425,f541])).

fof(f541,plain,(
    r2_hidden(k4_tarski(sK4(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f62,f192,f116])).

fof(f3425,plain,
    ( sK0 = sK4(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | ~ spl13_10
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f141,f193,f3192,f900])).

fof(f193,plain,(
    ~ r2_hidden(sK4(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f141,f87])).

fof(f3192,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl13_44 ),
    inference(avatar_component_clause,[],[f3191])).

fof(f3191,plain,
    ( spl13_44
  <=> r2_hidden(k4_tarski(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).

fof(f133,plain,(
    v4_relat_2(sK2) ),
    inference(unit_resulting_resolution,[],[f62,f63,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t33_wellord1.p',d4_wellord1)).

fof(f63,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f3396,plain,
    ( spl13_46
    | spl13_48
    | spl13_50
    | spl13_52
    | ~ spl13_14
    | spl13_45 ),
    inference(avatar_split_clause,[],[f3220,f3194,f438,f3394,f3388,f3382,f3376])).

fof(f438,plain,
    ( spl13_14
  <=> ! [X7,X8] :
        ( ~ r2_hidden(X7,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X8,X7),sK2)
        | r2_hidden(k4_tarski(X7,X8),sK2)
        | X7 = X8
        | ~ r2_hidden(X8,k3_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f3220,plain,
    ( sK0 = sK1
    | k1_wellord1(sK2,sK0) = k1_xboole_0
    | k1_wellord1(sK2,sK1) = k1_xboole_0
    | r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl13_14
    | ~ spl13_45 ),
    inference(resolution,[],[f3195,f1035])).

fof(f1035,plain,
    ( ! [X6,X5] :
        ( r2_hidden(k4_tarski(X6,X5),sK2)
        | X5 = X6
        | k1_wellord1(sK2,X5) = k1_xboole_0
        | k1_wellord1(sK2,X6) = k1_xboole_0
        | r2_hidden(X5,k1_wellord1(sK2,X6)) )
    | ~ spl13_14 ),
    inference(duplicate_literal_removal,[],[f1024])).

fof(f1024,plain,
    ( ! [X6,X5] :
        ( X5 = X6
        | r2_hidden(k4_tarski(X6,X5),sK2)
        | k1_wellord1(sK2,X5) = k1_xboole_0
        | k1_wellord1(sK2,X6) = k1_xboole_0
        | X5 = X6
        | r2_hidden(X5,k1_wellord1(sK2,X6)) )
    | ~ spl13_14 ),
    inference(resolution,[],[f712,f127])).

fof(f712,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | k1_wellord1(sK2,X0) = k1_xboole_0
        | k1_wellord1(sK2,X1) = k1_xboole_0 )
    | ~ spl13_14 ),
    inference(resolution,[],[f476,f120])).

fof(f120,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_relat_1(sK2))
      | k1_wellord1(sK2,X0) = k1_xboole_0 ) ),
    inference(resolution,[],[f62,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(X0,k3_relat_1(X1))
      | k1_wellord1(X1,X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k1_xboole_0
      | r2_hidden(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k1_xboole_0
      | r2_hidden(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord1(X1,X0) = k1_xboole_0
        | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t33_wellord1.p',t2_wellord1)).

fof(f476,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | X0 = X1
        | r2_hidden(k4_tarski(X0,X1),sK2)
        | k1_wellord1(sK2,X1) = k1_xboole_0 )
    | ~ spl13_14 ),
    inference(resolution,[],[f439,f120])).

fof(f439,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(X7,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X8,X7),sK2)
        | r2_hidden(k4_tarski(X7,X8),sK2)
        | X7 = X8
        | ~ r2_hidden(X8,k3_relat_1(sK2)) )
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f438])).

fof(f458,plain,(
    spl13_13 ),
    inference(avatar_contradiction_clause,[],[f449])).

fof(f449,plain,
    ( $false
    | ~ spl13_13 ),
    inference(unit_resulting_resolution,[],[f63,f62,f436,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f436,plain,
    ( ~ v6_relat_2(sK2)
    | ~ spl13_13 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl13_13
  <=> ~ v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f440,plain,
    ( ~ spl13_13
    | spl13_14 ),
    inference(avatar_split_clause,[],[f124,f438,f435])).

fof(f124,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X7,k3_relat_1(sK2))
      | ~ r2_hidden(X8,k3_relat_1(sK2))
      | X7 = X8
      | r2_hidden(k4_tarski(X7,X8),sK2)
      | r2_hidden(k4_tarski(X8,X7),sK2)
      | ~ v6_relat_2(sK2) ) ),
    inference(resolution,[],[f62,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | X1 = X2
      | r2_hidden(k4_tarski(X1,X2),X0)
      | r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t33_wellord1.p',l4_wellord1)).

fof(f365,plain,(
    spl13_9 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | ~ spl13_9 ),
    inference(unit_resulting_resolution,[],[f63,f62,f346,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f346,plain,
    ( ~ v8_relat_2(sK2)
    | ~ spl13_9 ),
    inference(avatar_component_clause,[],[f345])).

fof(f345,plain,
    ( spl13_9
  <=> ~ v8_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f350,plain,
    ( ~ spl13_9
    | spl13_10 ),
    inference(avatar_split_clause,[],[f125,f348,f345])).

fof(f125,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X9,X10),sK2)
      | ~ r2_hidden(k4_tarski(X10,X11),sK2)
      | r2_hidden(k4_tarski(X9,X11),sK2)
      | ~ v8_relat_2(sK2) ) ),
    inference(resolution,[],[f62,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(k4_tarski(X1,X3),X0)
      | ~ v8_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t33_wellord1.p',l2_wellord1)).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t123_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:14 EDT 2019

% Result     : Theorem 6.64s
% Output     : Refutation 6.64s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 399 expanded)
%              Number of leaves         :   19 ( 116 expanded)
%              Depth                    :   13
%              Number of atoms          :  357 (1248 expanded)
%              Number of equality atoms :   57 ( 291 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22261,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f136,f155,f421,f430,f809,f813,f3113,f3426,f21949,f22015,f22260])).

fof(f22260,plain,
    ( ~ spl11_0
    | ~ spl11_46
    | ~ spl11_106 ),
    inference(avatar_contradiction_clause,[],[f22249])).

fof(f22249,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_46
    | ~ spl11_106 ),
    inference(unit_resulting_resolution,[],[f49,f50,f21948,f22136,f100])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t123_funct_1.p',d12_funct_1)).

fof(f22136,plain,
    ( ~ r2_hidden(sK4(sK2,sK1,sK8(k9_relat_1(sK2,k4_xboole_0(sK0,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK1)
    | ~ spl11_0
    | ~ spl11_46
    | ~ spl11_106 ),
    inference(backward_demodulation,[],[f22105,f2843])).

fof(f2843,plain,
    ( ~ r2_hidden(sK4(sK2,k4_xboole_0(sK0,sK1),sK8(k9_relat_1(sK2,k4_xboole_0(sK0,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK1)
    | ~ spl11_0 ),
    inference(unit_resulting_resolution,[],[f142,f137])).

fof(f137,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK4(sK2,k4_xboole_0(X1,X2),X0),X2)
        | ~ r2_hidden(X0,k9_relat_1(sK2,k4_xboole_0(X1,X2))) )
    | ~ spl11_0 ),
    inference(resolution,[],[f125,f105])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t123_funct_1.p',d5_xboole_0)).

fof(f125,plain,
    ( ! [X6,X7] :
        ( r2_hidden(sK4(sK2,X6,X7),X6)
        | ~ r2_hidden(X7,k9_relat_1(sK2,X6)) )
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl11_0
  <=> ! [X7,X6] :
        ( r2_hidden(sK4(sK2,X6,X7),X6)
        | ~ r2_hidden(X7,k9_relat_1(sK2,X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f142,plain,(
    r2_hidden(sK8(k9_relat_1(sK2,k4_xboole_0(sK0,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,k4_xboole_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f114,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t123_funct_1.p',d3_tarski)).

fof(f114,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(unit_resulting_resolution,[],[f94,f107,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t123_funct_1.p',d10_xboole_0)).

fof(f107,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)),k9_relat_1(sK2,k4_xboole_0(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f49,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k4_xboole_0(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f54,f55,f55])).

fof(f55,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t123_funct_1.p',redefinition_k6_subset_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t123_funct_1.p',t155_relat_1)).

fof(f94,plain,(
    k9_relat_1(sK2,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(definition_unfolding,[],[f52,f55,f55])).

fof(f52,plain,(
    k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1))
      & v2_funct_1(X2)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1))
      & v2_funct_1(X2)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( v2_funct_1(X2)
         => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t123_funct_1.p',t123_funct_1)).

fof(f22105,plain,
    ( sK4(sK2,sK1,sK8(k9_relat_1(sK2,k4_xboole_0(sK0,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) = sK4(sK2,k4_xboole_0(sK0,sK1),sK8(k9_relat_1(sK2,k4_xboole_0(sK0,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))
    | ~ spl11_46
    | ~ spl11_106 ),
    inference(unit_resulting_resolution,[],[f2855,f2857,f21948,f3425])).

fof(f3425,plain,
    ( ! [X2,X0,X1] :
        ( k1_funct_1(sK2,X2) != X1
        | ~ r2_hidden(X1,k9_relat_1(sK2,X0))
        | ~ r2_hidden(X2,k1_relat_1(sK2))
        | sK4(sK2,X0,X1) = X2 )
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f3424])).

fof(f3424,plain,
    ( spl11_46
  <=> ! [X1,X0,X2] :
        ( sK4(sK2,X0,X1) = X2
        | ~ r2_hidden(X1,k9_relat_1(sK2,X0))
        | ~ r2_hidden(X2,k1_relat_1(sK2))
        | k1_funct_1(sK2,X2) != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f2857,plain,(
    k1_funct_1(sK2,sK4(sK2,k4_xboole_0(sK0,sK1),sK8(k9_relat_1(sK2,k4_xboole_0(sK0,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))) = sK8(k9_relat_1(sK2,k4_xboole_0(sK0,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(unit_resulting_resolution,[],[f50,f49,f142,f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK4(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2855,plain,(
    r2_hidden(sK4(sK2,k4_xboole_0(sK0,sK1),sK8(k9_relat_1(sK2,k4_xboole_0(sK0,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f50,f49,f142,f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0,X1,X3),k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f21948,plain,
    ( r2_hidden(sK8(k9_relat_1(sK2,k4_xboole_0(sK0,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1))
    | ~ spl11_106 ),
    inference(avatar_component_clause,[],[f21947])).

fof(f21947,plain,
    ( spl11_106
  <=> r2_hidden(sK8(k9_relat_1(sK2,k4_xboole_0(sK0,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_106])])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f22015,plain,
    ( ~ spl11_40
    | spl11_105 ),
    inference(avatar_contradiction_clause,[],[f21998])).

fof(f21998,plain,
    ( $false
    | ~ spl11_40
    | ~ spl11_105 ),
    inference(unit_resulting_resolution,[],[f142,f2856,f21942,f3150])).

fof(f3150,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r2_hidden(sK4(sK2,X6,X4),k4_xboole_0(X5,X7))
        | ~ r2_hidden(X4,k9_relat_1(sK2,X6))
        | r2_hidden(X4,k9_relat_1(sK2,X5)) )
    | ~ spl11_40 ),
    inference(resolution,[],[f3112,f106])).

fof(f106,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3112,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK4(sK2,X1,X0),X2)
        | r2_hidden(X0,k9_relat_1(sK2,X2))
        | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) )
    | ~ spl11_40 ),
    inference(avatar_component_clause,[],[f3111])).

fof(f3111,plain,
    ( spl11_40
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k9_relat_1(sK2,X1))
        | r2_hidden(X0,k9_relat_1(sK2,X2))
        | ~ r2_hidden(sK4(sK2,X1,X0),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).

fof(f21942,plain,
    ( ~ r2_hidden(sK8(k9_relat_1(sK2,k4_xboole_0(sK0,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))
    | ~ spl11_105 ),
    inference(avatar_component_clause,[],[f21941])).

fof(f21941,plain,
    ( spl11_105
  <=> ~ r2_hidden(sK8(k9_relat_1(sK2,k4_xboole_0(sK0,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_105])])).

fof(f2856,plain,(
    r2_hidden(sK4(sK2,k4_xboole_0(sK0,sK1),sK8(k9_relat_1(sK2,k4_xboole_0(sK0,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),k4_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f50,f49,f142,f100])).

fof(f21949,plain,
    ( ~ spl11_105
    | spl11_106 ),
    inference(avatar_split_clause,[],[f3232,f21947,f21941])).

fof(f3232,plain,
    ( r2_hidden(sK8(k9_relat_1(sK2,k4_xboole_0(sK0,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1))
    | ~ r2_hidden(sK8(k9_relat_1(sK2,k4_xboole_0(sK0,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f143,f104])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f143,plain,(
    ~ r2_hidden(sK8(k9_relat_1(sK2,k4_xboole_0(sK0,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(unit_resulting_resolution,[],[f114,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK8(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3426,plain,
    ( ~ spl11_3
    | ~ spl11_19
    | spl11_46
    | ~ spl11_4
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f911,f419,f153,f3424,f804,f130])).

fof(f130,plain,
    ( spl11_3
  <=> ~ v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f804,plain,
    ( spl11_19
  <=> ~ v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f153,plain,
    ( spl11_4
  <=> ! [X9,X8] :
        ( k1_funct_1(sK2,sK4(sK2,X8,X9)) = X9
        | ~ r2_hidden(X9,k9_relat_1(sK2,X8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f419,plain,
    ( spl11_10
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | X0 = X1
        | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1)
        | ~ r2_hidden(X1,k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f911,plain,
    ( ! [X2,X0,X1] :
        ( sK4(sK2,X0,X1) = X2
        | k1_funct_1(sK2,X2) != X1
        | ~ r2_hidden(X2,k1_relat_1(sK2))
        | ~ r2_hidden(X1,k9_relat_1(sK2,X0))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl11_4
    | ~ spl11_10 ),
    inference(duplicate_literal_removal,[],[f905])).

fof(f905,plain,
    ( ! [X2,X0,X1] :
        ( sK4(sK2,X0,X1) = X2
        | k1_funct_1(sK2,X2) != X1
        | ~ r2_hidden(X2,k1_relat_1(sK2))
        | ~ r2_hidden(X1,k9_relat_1(sK2,X0))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X1,k9_relat_1(sK2,X0)) )
    | ~ spl11_4
    | ~ spl11_10 ),
    inference(resolution,[],[f461,f101])).

fof(f461,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK4(sK2,X0,X1),k1_relat_1(sK2))
        | sK4(sK2,X0,X1) = X2
        | k1_funct_1(sK2,X2) != X1
        | ~ r2_hidden(X2,k1_relat_1(sK2))
        | ~ r2_hidden(X1,k9_relat_1(sK2,X0)) )
    | ~ spl11_4
    | ~ spl11_10 ),
    inference(superposition,[],[f420,f154])).

fof(f154,plain,
    ( ! [X8,X9] :
        ( k1_funct_1(sK2,sK4(sK2,X8,X9)) = X9
        | ~ r2_hidden(X9,k9_relat_1(sK2,X8)) )
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f153])).

fof(f420,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1)
        | X0 = X1
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(X1,k1_relat_1(sK2)) )
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f419])).

fof(f3113,plain,
    ( ~ spl11_3
    | ~ spl11_19
    | spl11_40
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f864,f807,f3111,f804,f130])).

fof(f807,plain,
    ( spl11_20
  <=> ! [X5,X4,X6] :
        ( r2_hidden(X5,k9_relat_1(sK2,X6))
        | ~ r2_hidden(X5,k9_relat_1(sK2,X4))
        | ~ r2_hidden(sK4(sK2,X4,X5),X6)
        | ~ r2_hidden(sK4(sK2,X4,X5),k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f864,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK2,X1))
        | ~ r2_hidden(sK4(sK2,X1,X0),X2)
        | r2_hidden(X0,k9_relat_1(sK2,X2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl11_20 ),
    inference(duplicate_literal_removal,[],[f858])).

fof(f858,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK2,X1))
        | ~ r2_hidden(sK4(sK2,X1,X0),X2)
        | r2_hidden(X0,k9_relat_1(sK2,X2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) )
    | ~ spl11_20 ),
    inference(resolution,[],[f808,f101])).

fof(f808,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_hidden(sK4(sK2,X4,X5),k1_relat_1(sK2))
        | ~ r2_hidden(X5,k9_relat_1(sK2,X4))
        | ~ r2_hidden(sK4(sK2,X4,X5),X6)
        | r2_hidden(X5,k9_relat_1(sK2,X6)) )
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f807])).

fof(f813,plain,(
    spl11_19 ),
    inference(avatar_contradiction_clause,[],[f810])).

fof(f810,plain,
    ( $false
    | ~ spl11_19 ),
    inference(unit_resulting_resolution,[],[f50,f805])).

fof(f805,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f804])).

fof(f809,plain,
    ( ~ spl11_3
    | ~ spl11_19
    | spl11_20
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f157,f153,f807,f804,f130])).

fof(f157,plain,
    ( ! [X6,X4,X5] :
        ( r2_hidden(X5,k9_relat_1(sK2,X6))
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(sK4(sK2,X4,X5),k1_relat_1(sK2))
        | ~ r2_hidden(sK4(sK2,X4,X5),X6)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X5,k9_relat_1(sK2,X4)) )
    | ~ spl11_4 ),
    inference(superposition,[],[f98,f154])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | r2_hidden(k1_funct_1(X0,X4),X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | k1_funct_1(X0,X4) != X3
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f430,plain,(
    spl11_9 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | ~ spl11_9 ),
    inference(unit_resulting_resolution,[],[f51,f417])).

fof(f417,plain,
    ( ~ v2_funct_1(sK2)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl11_9
  <=> ~ v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f51,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f421,plain,
    ( ~ spl11_9
    | spl11_10
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f108,f130,f419,f416])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1)
      | X0 = X1
      | ~ v2_funct_1(sK2) ) ),
    inference(resolution,[],[f50,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t123_funct_1.p',d8_funct_1)).

fof(f155,plain,
    ( spl11_4
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f112,f130,f153])).

fof(f112,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,sK4(sK2,X8,X9)) = X9
      | ~ r2_hidden(X9,k9_relat_1(sK2,X8)) ) ),
    inference(resolution,[],[f50,f99])).

fof(f136,plain,(
    spl11_3 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | ~ spl11_3 ),
    inference(unit_resulting_resolution,[],[f49,f131])).

fof(f131,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( spl11_0
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f111,f130,f124])).

fof(f111,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(sK2)
      | r2_hidden(sK4(sK2,X6,X7),X6)
      | ~ r2_hidden(X7,k9_relat_1(sK2,X6)) ) ),
    inference(resolution,[],[f50,f100])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t37_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:13 EDT 2019

% Result     : Theorem 7.67s
% Output     : Refutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 533 expanded)
%              Number of leaves         :   24 ( 136 expanded)
%              Depth                    :   14
%              Number of atoms          :  401 (2079 expanded)
%              Number of equality atoms :   27 (  80 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1681,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f154,f198,f405,f420,f458,f476,f603,f612,f621,f723,f806,f994,f1563,f1680])).

fof(f1680,plain,
    ( ~ spl14_0
    | spl14_3
    | ~ spl14_26 ),
    inference(avatar_contradiction_clause,[],[f1671])).

fof(f1671,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_3
    | ~ spl14_26 ),
    inference(unit_resulting_resolution,[],[f1200,f1641,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t37_wellord1.p',t1_subset)).

fof(f1641,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK0))
    | ~ spl14_0
    | ~ spl14_3
    | ~ spl14_26 ),
    inference(backward_demodulation,[],[f590,f1505])).

fof(f1505,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl14_0
    | ~ spl14_3 ),
    inference(backward_demodulation,[],[f1498,f950])).

fof(f950,plain,
    ( r2_hidden(sK3(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f150,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/wellord1__t37_wellord1.p',d3_tarski)).

fof(f150,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl14_3
  <=> ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f1498,plain,
    ( sK1 = sK3(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl14_0
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f55,f951,f1460,f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | X1 = X3
      | ~ r2_hidden(k4_tarski(X3,X1),X0)
      | r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | X1 = X3
      | ~ r2_hidden(k4_tarski(X3,X1),X0)
      | r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/wellord1__t37_wellord1.p',d1_wellord1)).

fof(f1460,plain,
    ( r2_hidden(k4_tarski(sK3(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2)
    | ~ spl14_0
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f118,f55,f147,f949,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(k4_tarski(X1,X3),X0)
      | ~ v8_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox2/benchmark/wellord1__t37_wellord1.p',l2_wellord1)).

fof(f949,plain,
    ( r2_hidden(k4_tarski(sK3(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK0),sK2)
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f150,f243])).

fof(f243,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(sK2,X0),X1)
      | r2_hidden(k4_tarski(sK3(k1_wellord1(sK2,X0),X1),X0),sK2) ) ),
    inference(resolution,[],[f114,f62])).

fof(f114,plain,(
    ! [X17,X16] :
      ( ~ r2_hidden(X16,k1_wellord1(sK2,X17))
      | r2_hidden(k4_tarski(X16,X17),sK2) ) ),
    inference(resolution,[],[f55,f102])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f147,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl14_0 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl14_0
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_0])])).

fof(f118,plain,(
    v8_relat_2(sK2) ),
    inference(unit_resulting_resolution,[],[f55,f56,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox2/benchmark/wellord1__t37_wellord1.p',d4_wellord1)).

fof(f56,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r2_hidden(k4_tarski(X0,X1),X2)
          <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t37_wellord1.p',t37_wellord1)).

fof(f951,plain,
    ( ~ r2_hidden(sK3(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f150,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f590,plain,
    ( sK0 = sK1
    | ~ spl14_26 ),
    inference(avatar_component_clause,[],[f589])).

fof(f589,plain,
    ( spl14_26
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_26])])).

fof(f1200,plain,
    ( ~ m1_subset_1(sK0,k1_wellord1(sK2,sK0))
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f105,f1196,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t37_wellord1.p',t2_subset)).

fof(f1196,plain,
    ( ~ v1_xboole_0(k1_wellord1(sK2,sK0))
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f950,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t37_wellord1.p',t7_boole)).

fof(f105,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_wellord1(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f55,f104])).

fof(f104,plain,(
    ! [X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k1_wellord1(X0,X3)) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | X1 != X3
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1563,plain,
    ( ~ spl14_0
    | spl14_3
    | spl14_27 ),
    inference(avatar_contradiction_clause,[],[f1553])).

fof(f1553,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_3
    | ~ spl14_27 ),
    inference(unit_resulting_resolution,[],[f1201,f1505,f88])).

fof(f1201,plain,
    ( ~ m1_subset_1(sK1,k1_wellord1(sK2,sK0))
    | ~ spl14_0
    | ~ spl14_3
    | ~ spl14_27 ),
    inference(unit_resulting_resolution,[],[f1159,f1196,f89])).

fof(f1159,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl14_0
    | ~ spl14_27 ),
    inference(unit_resulting_resolution,[],[f55,f916,f102])).

fof(f916,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl14_0
    | ~ spl14_27 ),
    inference(unit_resulting_resolution,[],[f119,f55,f587,f147,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(k4_tarski(X2,X1),X0)
      | X1 = X2
      | ~ v4_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox2/benchmark/wellord1__t37_wellord1.p',l3_wellord1)).

fof(f587,plain,
    ( sK0 != sK1
    | ~ spl14_27 ),
    inference(avatar_component_clause,[],[f586])).

fof(f586,plain,
    ( spl14_27
  <=> sK0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_27])])).

fof(f119,plain,(
    v4_relat_2(sK2) ),
    inference(unit_resulting_resolution,[],[f55,f56,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f994,plain,
    ( ~ spl14_0
    | ~ spl14_14
    | spl14_27
    | ~ spl14_28 ),
    inference(avatar_contradiction_clause,[],[f984])).

fof(f984,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_14
    | ~ spl14_27
    | ~ spl14_28 ),
    inference(unit_resulting_resolution,[],[f119,f55,f587,f147,f780,f92])).

fof(f780,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl14_14
    | ~ spl14_28 ),
    inference(unit_resulting_resolution,[],[f133,f596,f404])).

fof(f404,plain,
    ( ! [X12,X13,X11] :
        ( ~ r2_hidden(k4_tarski(X11,X12),sK2)
        | r2_hidden(k4_tarski(X11,X13),sK2)
        | ~ r2_hidden(k4_tarski(X12,X13),sK2) )
    | ~ spl14_14 ),
    inference(avatar_component_clause,[],[f403])).

fof(f403,plain,
    ( spl14_14
  <=> ! [X11,X13,X12] :
        ( ~ r2_hidden(k4_tarski(X11,X12),sK2)
        | r2_hidden(k4_tarski(X11,X13),sK2)
        | ~ r2_hidden(k4_tarski(X12,X13),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f596,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl14_28 ),
    inference(avatar_component_clause,[],[f595])).

fof(f595,plain,
    ( spl14_28
  <=> r2_hidden(k4_tarski(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_28])])).

fof(f133,plain,(
    r2_hidden(k4_tarski(sK1,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f117,f55,f58,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X1),X0)
      | ~ v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t37_wellord1.p',l1_wellord1)).

fof(f58,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f117,plain,(
    v1_relat_2(sK2) ),
    inference(unit_resulting_resolution,[],[f55,f56,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f806,plain,
    ( ~ spl14_2
    | spl14_27
    | ~ spl14_28 ),
    inference(avatar_contradiction_clause,[],[f799])).

fof(f799,plain,
    ( $false
    | ~ spl14_2
    | ~ spl14_27
    | ~ spl14_28 ),
    inference(unit_resulting_resolution,[],[f55,f587,f179,f596,f101])).

fof(f179,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl14_2 ),
    inference(unit_resulting_resolution,[],[f105,f153,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f153,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl14_2
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f723,plain,
    ( spl14_1
    | ~ spl14_26 ),
    inference(avatar_contradiction_clause,[],[f711])).

fof(f711,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_26 ),
    inference(unit_resulting_resolution,[],[f163,f162,f626,f89])).

fof(f626,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK0),sK2)
    | ~ spl14_1
    | ~ spl14_26 ),
    inference(backward_demodulation,[],[f590,f144])).

fof(f144,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl14_1
  <=> ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f162,plain,(
    m1_subset_1(k4_tarski(sK0,sK0),sK2) ),
    inference(unit_resulting_resolution,[],[f125,f88])).

fof(f125,plain,(
    r2_hidden(k4_tarski(sK0,sK0),sK2) ),
    inference(unit_resulting_resolution,[],[f117,f55,f57,f77])).

fof(f57,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f163,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f125,f100])).

fof(f621,plain,(
    spl14_31 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | ~ spl14_31 ),
    inference(unit_resulting_resolution,[],[f129,f136,f602,f89])).

fof(f602,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl14_31 ),
    inference(avatar_component_clause,[],[f601])).

fof(f601,plain,
    ( spl14_31
  <=> ~ r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_31])])).

fof(f136,plain,(
    m1_subset_1(sK1,k3_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f58,f88])).

fof(f129,plain,(
    ~ v1_xboole_0(k3_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f57,f100])).

fof(f612,plain,(
    spl14_25 ),
    inference(avatar_contradiction_clause,[],[f607])).

fof(f607,plain,
    ( $false
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f129,f128,f584,f89])).

fof(f584,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl14_25 ),
    inference(avatar_component_clause,[],[f583])).

fof(f583,plain,
    ( spl14_25
  <=> ~ r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_25])])).

fof(f128,plain,(
    m1_subset_1(sK0,k3_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f57,f88])).

fof(f603,plain,
    ( ~ spl14_25
    | spl14_26
    | spl14_28
    | ~ spl14_31
    | spl14_1
    | ~ spl14_18 ),
    inference(avatar_split_clause,[],[f497,f456,f143,f601,f595,f589,f583])).

fof(f456,plain,
    ( spl14_18
  <=> ! [X7,X6] :
        ( ~ r2_hidden(X6,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X7,X6),sK2)
        | r2_hidden(k4_tarski(X6,X7),sK2)
        | X6 = X7
        | ~ r2_hidden(X7,k3_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).

fof(f497,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK2))
    | r2_hidden(k4_tarski(sK1,sK0),sK2)
    | sK0 = sK1
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl14_1
    | ~ spl14_18 ),
    inference(resolution,[],[f457,f144])).

fof(f457,plain,
    ( ! [X6,X7] :
        ( r2_hidden(k4_tarski(X7,X6),sK2)
        | ~ r2_hidden(X6,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X6,X7),sK2)
        | X6 = X7
        | ~ r2_hidden(X7,k3_relat_1(sK2)) )
    | ~ spl14_18 ),
    inference(avatar_component_clause,[],[f456])).

fof(f476,plain,(
    spl14_17 ),
    inference(avatar_contradiction_clause,[],[f462])).

fof(f462,plain,
    ( $false
    | ~ spl14_17 ),
    inference(unit_resulting_resolution,[],[f56,f55,f454,f83])).

fof(f83,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f454,plain,
    ( ~ v6_relat_2(sK2)
    | ~ spl14_17 ),
    inference(avatar_component_clause,[],[f453])).

fof(f453,plain,
    ( spl14_17
  <=> ~ v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).

fof(f458,plain,
    ( ~ spl14_17
    | spl14_18 ),
    inference(avatar_split_clause,[],[f109,f456,f453])).

fof(f109,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k3_relat_1(sK2))
      | ~ r2_hidden(X7,k3_relat_1(sK2))
      | X6 = X7
      | r2_hidden(k4_tarski(X6,X7),sK2)
      | r2_hidden(k4_tarski(X7,X6),sK2)
      | ~ v6_relat_2(sK2) ) ),
    inference(resolution,[],[f55,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | X1 = X2
      | r2_hidden(k4_tarski(X1,X2),X0)
      | r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/wellord1__t37_wellord1.p',l4_wellord1)).

fof(f420,plain,(
    spl14_13 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | ~ spl14_13 ),
    inference(unit_resulting_resolution,[],[f56,f55,f401,f81])).

fof(f401,plain,
    ( ~ v8_relat_2(sK2)
    | ~ spl14_13 ),
    inference(avatar_component_clause,[],[f400])).

fof(f400,plain,
    ( spl14_13
  <=> ~ v8_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).

fof(f405,plain,
    ( ~ spl14_13
    | spl14_14 ),
    inference(avatar_split_clause,[],[f112,f403,f400])).

fof(f112,plain,(
    ! [X12,X13,X11] :
      ( ~ r2_hidden(k4_tarski(X11,X12),sK2)
      | ~ r2_hidden(k4_tarski(X12,X13),sK2)
      | r2_hidden(k4_tarski(X11,X13),sK2)
      | ~ v8_relat_2(sK2) ) ),
    inference(resolution,[],[f55,f96])).

fof(f198,plain,
    ( ~ spl14_1
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f54,f149,f143])).

fof(f54,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f154,plain,
    ( spl14_0
    | spl14_2 ),
    inference(avatar_split_clause,[],[f53,f152,f146])).

fof(f53,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------

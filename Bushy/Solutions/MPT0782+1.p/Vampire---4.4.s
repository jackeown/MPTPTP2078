%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t31_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:13 EDT 2019

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 170 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   26
%              Number of atoms          :  371 ( 574 expanded)
%              Number of equality atoms :   28 (  41 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1774,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f108,f119,f1664,f1695,f1698,f1761,f1773])).

fof(f1773,plain,
    ( ~ spl6_0
    | spl6_13 ),
    inference(avatar_contradiction_clause,[],[f1772])).

fof(f1772,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f1769,f100])).

fof(f100,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f1769,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl6_13 ),
    inference(resolution,[],[f1760,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t31_wellord1.p',t20_wellord1)).

fof(f1760,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f1759])).

fof(f1759,plain,
    ( spl6_13
  <=> ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f1761,plain,
    ( ~ spl6_13
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f1750,f1690,f1656,f117,f1759])).

fof(f117,plain,
    ( spl6_5
  <=> ~ v1_wellord1(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f1656,plain,
    ( spl6_6
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k3_relat_1(sK1))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,sK0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1690,plain,
    ( spl6_10
  <=> v1_relat_1(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f1750,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f1749,f118])).

fof(f118,plain,
    ( ~ v1_wellord1(k2_wellord1(sK1,sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f1749,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | v1_wellord1(k2_wellord1(sK1,sK0))
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f1746,f1691])).

fof(f1691,plain,
    ( v1_relat_1(k2_wellord1(sK1,sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f1690])).

fof(f1746,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | v1_wellord1(k2_wellord1(sK1,sK0))
    | ~ spl6_6 ),
    inference(resolution,[],[f1657,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r1_tarski(sK2(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_wellord1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                & r2_hidden(X2,X1) )
            | k1_xboole_0 = X1
            | ~ r1_tarski(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> ! [X1] :
            ~ ( ! [X2] :
                  ~ ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t31_wellord1.p',d2_wellord1)).

fof(f1657,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,sK0)),X0)
        | ~ r1_tarski(X0,k3_relat_1(sK1)) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f1656])).

fof(f1698,plain,
    ( ~ spl6_0
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f1697])).

fof(f1697,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f1696,f100])).

fof(f1696,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl6_11 ),
    inference(resolution,[],[f1694,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t31_wellord1.p',dt_k2_wellord1)).

fof(f1694,plain,
    ( ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f1693])).

fof(f1693,plain,
    ( spl6_11
  <=> ~ v1_relat_1(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f1695,plain,
    ( ~ spl6_11
    | spl6_5
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f1685,f1662,f117,f1693])).

fof(f1662,plain,
    ( spl6_8
  <=> k1_xboole_0 = sK2(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f1685,plain,
    ( ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f1677,f118])).

fof(f1677,plain,
    ( ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | v1_wellord1(k2_wellord1(sK1,sK0))
    | ~ spl6_8 ),
    inference(trivial_inequality_removal,[],[f1676])).

fof(f1676,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | v1_wellord1(k2_wellord1(sK1,sK0))
    | ~ spl6_8 ),
    inference(superposition,[],[f70,f1663])).

fof(f1663,plain,
    ( k1_xboole_0 = sK2(k2_wellord1(sK1,sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f1662])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 != sK2(X0)
      | ~ v1_relat_1(X0)
      | v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1664,plain,
    ( spl6_6
    | spl6_8
    | ~ spl6_0
    | ~ spl6_2
    | spl6_5 ),
    inference(avatar_split_clause,[],[f1648,f117,f106,f99,f1662,f1656])).

fof(f106,plain,
    ( spl6_2
  <=> v1_wellord1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1648,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK2(k2_wellord1(sK1,sK0))
        | ~ r1_tarski(X0,k3_relat_1(sK1))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,sK0)),X0) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(resolution,[],[f1630,f118])).

fof(f1630,plain,
    ( ! [X0,X1] :
        ( v1_wellord1(k2_wellord1(sK1,X0))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | ~ r1_tarski(X1,k3_relat_1(sK1))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),X1) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f1621,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t31_wellord1.p',t1_xboole_1)).

fof(f1621,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | v1_wellord1(k2_wellord1(sK1,X0)) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f1616,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t31_wellord1.p',t3_subset)).

fof(f1616,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(k2_wellord1(sK1,X0)),k1_zfmisc_1(k3_relat_1(sK1)))
        | v1_wellord1(k2_wellord1(sK1,X0))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0)) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f1614,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1614,plain,
    ( ! [X0] :
        ( v1_wellord1(k2_wellord1(sK1,X0))
        | ~ m1_subset_1(sK2(k2_wellord1(sK1,X0)),k1_zfmisc_1(k3_relat_1(sK1)))
        | k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1)) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f1609,f111])).

fof(f111,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK1,X0),X0)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k3_relat_1(sK1)) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f109,f100])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_relat_1(sK1))
        | k1_xboole_0 = X0
        | r2_hidden(sK3(sK1,X0),X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl6_2 ),
    inference(resolution,[],[f107,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_wellord1(X0)
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | k1_xboole_0 = X1
      | r2_hidden(sK3(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f107,plain,
    ( v1_wellord1(sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f1609,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3(sK1,sK2(k2_wellord1(sK1,X2))),sK2(k2_wellord1(sK1,X2)))
        | v1_wellord1(k2_wellord1(sK1,X2))
        | ~ m1_subset_1(sK2(k2_wellord1(sK1,X2)),k1_zfmisc_1(k3_relat_1(sK1))) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f1593,f88])).

fof(f1593,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | ~ r2_hidden(sK3(sK1,sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | v1_wellord1(k2_wellord1(sK1,X0)) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f1592,f100])).

fof(f1592,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1,sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | v1_wellord1(k2_wellord1(sK1,X0))
        | ~ v1_relat_1(sK1) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f519,f80])).

fof(f519,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k2_wellord1(sK1,X0))
        | ~ r2_hidden(sK3(sK1,sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | v1_wellord1(k2_wellord1(sK1,X0)) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f516,f70])).

fof(f516,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK2(k2_wellord1(sK1,X0))
        | ~ r1_tarski(sK2(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | ~ r2_hidden(sK3(sK1,sK2(k2_wellord1(sK1,X0))),sK2(k2_wellord1(sK1,X0)))
        | ~ v1_relat_1(k2_wellord1(sK1,X0))
        | v1_wellord1(k2_wellord1(sK1,X0)) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f514,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r1_xboole_0(k1_wellord1(X0,X2),sK2(X0))
      | ~ r2_hidden(X2,sK2(X0))
      | ~ v1_relat_1(X0)
      | v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f514,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_wellord1(k2_wellord1(sK1,X1),sK3(sK1,X0)),X0)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k3_relat_1(sK1)) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(duplicate_literal_removal,[],[f512])).

fof(f512,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k3_relat_1(sK1))
        | k1_xboole_0 = X0
        | r1_xboole_0(k1_wellord1(k2_wellord1(sK1,X1),sK3(sK1,X0)),X0)
        | r1_xboole_0(k1_wellord1(k2_wellord1(sK1,X1),sK3(sK1,X0)),X0) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f230,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t31_wellord1.p',t3_xboole_0)).

fof(f230,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(sK5(k1_wellord1(k2_wellord1(sK1,X3),sK3(sK1,X4)),X5),X4)
        | ~ r1_tarski(X4,k3_relat_1(sK1))
        | k1_xboole_0 = X4
        | r1_xboole_0(k1_wellord1(k2_wellord1(sK1,X3),sK3(sK1,X4)),X5) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f203,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f203,plain,
    ( ! [X12,X10,X11] :
        ( ~ r2_hidden(X11,k1_wellord1(k2_wellord1(sK1,X12),sK3(sK1,X10)))
        | ~ r2_hidden(X11,X10)
        | ~ r1_tarski(X10,k3_relat_1(sK1))
        | k1_xboole_0 = X10 )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f202,f100])).

fof(f202,plain,
    ( ! [X12,X10,X11] :
        ( ~ r1_tarski(X10,k3_relat_1(sK1))
        | ~ r2_hidden(X11,X10)
        | ~ r2_hidden(X11,k1_wellord1(k2_wellord1(sK1,X12),sK3(sK1,X10)))
        | k1_xboole_0 = X10
        | ~ v1_relat_1(sK1) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f165,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t31_wellord1.p',t21_wellord1)).

fof(f165,plain,
    ( ! [X4,X2,X3] :
        ( ~ r1_tarski(X4,k1_wellord1(sK1,sK3(sK1,X2)))
        | ~ r1_tarski(X2,k3_relat_1(sK1))
        | ~ r2_hidden(X3,X2)
        | ~ r2_hidden(X3,X4)
        | k1_xboole_0 = X2 )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f151,f87])).

fof(f151,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_wellord1(sK1,sK3(sK1,X2))))
        | k1_xboole_0 = X2
        | ~ r1_tarski(X2,k3_relat_1(sK1))
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X1,X3) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f149,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t31_wellord1.p',t5_subset)).

fof(f149,plain,
    ( ! [X2,X3,X1] :
        ( ~ r2_hidden(X1,X2)
        | k1_xboole_0 = X2
        | v1_xboole_0(k1_wellord1(sK1,sK3(sK1,X2)))
        | ~ r1_tarski(X2,k3_relat_1(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_wellord1(sK1,sK3(sK1,X2))))
        | ~ r2_hidden(X1,X3) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f132,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t31_wellord1.p',t4_subset)).

fof(f132,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X5,k1_wellord1(sK1,sK3(sK1,X4)))
        | ~ r2_hidden(X5,X4)
        | k1_xboole_0 = X4
        | v1_xboole_0(k1_wellord1(sK1,sK3(sK1,X4)))
        | ~ r1_tarski(X4,k3_relat_1(sK1)) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f124,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t31_wellord1.p',t2_subset)).

fof(f124,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k1_wellord1(sK1,sK3(sK1,X1)))
        | ~ r1_tarski(X1,k3_relat_1(sK1))
        | ~ r2_hidden(X2,X1)
        | k1_xboole_0 = X1 )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f112,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f112,plain,
    ( ! [X1] :
        ( r1_xboole_0(k1_wellord1(sK1,sK3(sK1,X1)),X1)
        | k1_xboole_0 = X1
        | ~ r1_tarski(X1,k3_relat_1(sK1)) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f110,f100])).

fof(f110,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k3_relat_1(sK1))
        | k1_xboole_0 = X1
        | r1_xboole_0(k1_wellord1(sK1,sK3(sK1,X1)),X1)
        | ~ v1_relat_1(sK1) )
    | ~ spl6_2 ),
    inference(resolution,[],[f107,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_wellord1(X0)
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | k1_xboole_0 = X1
      | r1_xboole_0(k1_wellord1(X0,sK3(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f119,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f62,f117])).

fof(f62,plain,(
    ~ v1_wellord1(k2_wellord1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ~ v1_wellord1(k2_wellord1(X1,X0))
      & v1_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ~ v1_wellord1(k2_wellord1(X1,X0))
      & v1_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v1_wellord1(X1)
         => v1_wellord1(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
       => v1_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t31_wellord1.p',t31_wellord1)).

fof(f108,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f61,f106])).

fof(f61,plain,(
    v1_wellord1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f60,f99])).

fof(f60,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------

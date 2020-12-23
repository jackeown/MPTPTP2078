%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t164_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:18 EDT 2019

% Result     : Theorem 0.95s
% Output     : Refutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 263 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :   20
%              Number of atoms          :  381 ( 902 expanded)
%              Number of equality atoms :   31 (  77 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1732,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f88,f95,f102,f109,f129,f142,f151,f451,f611,f1720,f1731])).

fof(f1731,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | spl7_17 ),
    inference(avatar_contradiction_clause,[],[f1730])).

fof(f1730,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f1715,f65])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t164_funct_1.p',d10_xboole_0)).

fof(f1715,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_17 ),
    inference(resolution,[],[f1673,f141])).

fof(f141,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl7_17
  <=> ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f1673,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
        | ~ r1_tarski(X0,sK0) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f1651])).

fof(f1651,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
        | ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f1648,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t164_funct_1.p',d3_tarski)).

fof(f1648,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK6(X0,k10_relat_1(sK1,k9_relat_1(sK1,X1))),X1)
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X1)))
        | ~ r1_tarski(X0,sK0) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1647,f87])).

fof(f87,plain,
    ( v1_funct_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl7_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1647,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK1)
        | ~ r2_hidden(sK6(X0,k10_relat_1(sK1,k9_relat_1(sK1,X1))),X1)
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X1)))
        | ~ r1_tarski(X0,sK0) )
    | ~ spl7_0
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1646,f80])).

fof(f80,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl7_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f1646,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ r2_hidden(sK6(X0,k10_relat_1(sK1,k9_relat_1(sK1,X1))),X1)
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X1)))
        | ~ r1_tarski(X0,sK0) )
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f1627])).

fof(f1627,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ r2_hidden(sK6(X0,k10_relat_1(sK1,k9_relat_1(sK1,X1))),X1)
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X1)))
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X1)))
        | ~ r1_tarski(X0,sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f244,f170])).

fof(f170,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(X0,X1),k1_relat_1(sK1))
        | r1_tarski(X0,X1)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f159,f101])).

fof(f101,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_6
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f159,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | r1_tarski(X2,X4)
      | r2_hidden(sK6(X2,X4),X5)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f145,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f62,f63])).

fof(f244,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(sK6(X7,k10_relat_1(X8,k9_relat_1(X8,X9))),k1_relat_1(X8))
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | ~ r2_hidden(sK6(X7,k10_relat_1(X8,k9_relat_1(X8,X9))),X9)
      | r1_tarski(X7,k10_relat_1(X8,k9_relat_1(X8,X9))) ) ),
    inference(resolution,[],[f176,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f176,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X4,k10_relat_1(X3,k9_relat_1(X3,X5)))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X4,X5) ) ),
    inference(duplicate_literal_removal,[],[f175])).

fof(f175,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_1(X3)
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_relat_1(X3)
      | r2_hidden(X4,k10_relat_1(X3,k9_relat_1(X3,X5)))
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ r2_hidden(X4,X5)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f72,f68])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | r2_hidden(k1_funct_1(X0,X4),X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | k1_funct_1(X0,X4) != X3
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t164_funct_1.p',d12_funct_1)).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t164_funct_1.p',d13_funct_1)).

fof(f1720,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | spl7_9
    | ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f1719])).

fof(f1719,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f1718,f108])).

fof(f108,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl7_9
  <=> k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f1718,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f1717,f65])).

fof(f1717,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(duplicate_literal_removal,[],[f1688])).

fof(f1688,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ r1_tarski(sK0,sK0)
    | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(resolution,[],[f1673,f747])).

fof(f747,plain,
    ( ! [X5] :
        ( ~ r1_tarski(X5,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
        | ~ r1_tarski(sK0,X5)
        | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = X5 )
    | ~ spl7_14 ),
    inference(resolution,[],[f719,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f719,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0)
        | ~ r1_tarski(sK0,X0) )
    | ~ spl7_14 ),
    inference(duplicate_literal_removal,[],[f710])).

fof(f710,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0)
        | ~ r1_tarski(sK0,X0)
        | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0) )
    | ~ spl7_14 ),
    inference(resolution,[],[f362,f64])).

fof(f362,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0),X1)
        | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0)
        | ~ r1_tarski(sK0,X1) )
    | ~ spl7_14 ),
    inference(resolution,[],[f240,f62])).

fof(f240,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0),sK0)
        | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0) )
    | ~ spl7_14 ),
    inference(resolution,[],[f173,f65])).

fof(f173,plain,
    ( ! [X10,X9] :
        ( ~ r1_tarski(X9,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
        | r2_hidden(sK6(X9,X10),sK0)
        | r1_tarski(X9,X10) )
    | ~ spl7_14 ),
    inference(resolution,[],[f159,f132])).

fof(f132,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl7_14
  <=> r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f611,plain,
    ( spl7_20
    | ~ spl7_23
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f511,f449,f609,f603])).

fof(f603,plain,
    ( spl7_20
  <=> k1_relat_1(sK1) = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f609,plain,
    ( spl7_23
  <=> ~ r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f449,plain,
    ( spl7_18
  <=> r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f511,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | k1_relat_1(sK1) = k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    | ~ spl7_18 ),
    inference(resolution,[],[f450,f44])).

fof(f450,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f449])).

fof(f451,plain,
    ( spl7_18
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f395,f131,f100,f449])).

fof(f395,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(duplicate_literal_removal,[],[f393])).

fof(f393,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(resolution,[],[f333,f64])).

fof(f333,plain,
    ( ! [X8] :
        ( r2_hidden(sK6(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X8),k1_relat_1(sK1))
        | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X8) )
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f332,f65])).

fof(f332,plain,
    ( ! [X8] :
        ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X8)
        | r2_hidden(sK6(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X8),k1_relat_1(sK1))
        | ~ r1_tarski(sK0,sK0) )
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(resolution,[],[f208,f132])).

fof(f208,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | r1_tarski(X1,X2)
        | r2_hidden(sK6(X1,X2),k1_relat_1(sK1))
        | ~ r1_tarski(X0,sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f190,f159])).

fof(f190,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_relat_1(sK1))
        | ~ r1_tarski(X0,sK0) )
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_relat_1(sK1))
        | ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,k1_relat_1(sK1)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f170,f64])).

fof(f151,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f149,f80])).

fof(f149,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f148,f94])).

fof(f94,plain,
    ( v2_funct_1(sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_4
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f148,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f146,f87])).

fof(f146,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_15 ),
    inference(resolution,[],[f59,f135])).

fof(f135,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl7_15
  <=> ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t164_funct_1.p',t152_funct_1)).

fof(f142,plain,
    ( ~ spl7_15
    | ~ spl7_17
    | spl7_9 ),
    inference(avatar_split_clause,[],[f113,f107,f140,f134])).

fof(f113,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | ~ spl7_9 ),
    inference(extensionality_resolution,[],[f44,f108])).

fof(f129,plain,
    ( spl7_10
    | ~ spl7_13
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f115,f100,f127,f121])).

fof(f121,plain,
    ( spl7_10
  <=> k1_relat_1(sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f127,plain,
    ( spl7_13
  <=> ~ r1_tarski(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f115,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | k1_relat_1(sK1) = sK0
    | ~ spl7_6 ),
    inference(resolution,[],[f44,f101])).

fof(f109,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f40,f107])).

fof(f40,plain,(
    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t164_funct_1.p',t164_funct_1)).

fof(f102,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f38,f100])).

fof(f38,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f95,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f39,f93])).

fof(f39,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f37,f86])).

fof(f37,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f36,f79])).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------

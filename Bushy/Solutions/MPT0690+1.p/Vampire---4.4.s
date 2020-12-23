%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t145_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:16 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 120 expanded)
%              Number of leaves         :   10 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  210 ( 355 expanded)
%              Number of equality atoms :   20 (  28 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f601,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f74,f81,f305,f500,f574,f577,f600])).

fof(f600,plain,
    ( spl7_5
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f599])).

fof(f599,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f597,f80])).

fof(f80,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl7_5
  <=> ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f597,plain,
    ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)
    | ~ spl7_10 ),
    inference(resolution,[],[f499,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t145_funct_1.p',d3_tarski)).

fof(f499,plain,
    ( r2_hidden(sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0),sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f498])).

fof(f498,plain,
    ( spl7_10
  <=> r2_hidden(sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f577,plain,
    ( spl7_5
    | spl7_9 ),
    inference(avatar_contradiction_clause,[],[f576])).

fof(f576,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f575,f80])).

fof(f575,plain,
    ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f572,f84])).

fof(f84,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f38,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f572,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)
    | ~ spl7_9 ),
    inference(resolution,[],[f493,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f36,f37])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f493,plain,
    ( ~ r2_hidden(sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f492])).

fof(f492,plain,
    ( spl7_9
  <=> ~ r2_hidden(sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0),k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f574,plain,
    ( spl7_5
    | spl7_9 ),
    inference(avatar_contradiction_clause,[],[f573])).

fof(f573,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f571,f80])).

fof(f571,plain,
    ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)
    | ~ spl7_9 ),
    inference(resolution,[],[f493,f37])).

fof(f500,plain,
    ( ~ spl7_9
    | spl7_10
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f429,f303,f72,f65,f498,f492])).

fof(f65,plain,
    ( spl7_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f72,plain,
    ( spl7_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f303,plain,
    ( spl7_6
  <=> k1_funct_1(sK1,sK4(sK1,k10_relat_1(sK1,sK0),sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0))) = sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f429,plain,
    ( r2_hidden(sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0),sK0)
    | ~ r2_hidden(sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f428,f66])).

fof(f66,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f65])).

fof(f428,plain,
    ( r2_hidden(sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0),sK0)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f424,f73])).

fof(f73,plain,
    ( v1_funct_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f424,plain,
    ( r2_hidden(sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f366,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t145_funct_1.p',d12_funct_1)).

fof(f366,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK4(sK1,k10_relat_1(sK1,sK0),sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)),k10_relat_1(sK1,X4))
        | r2_hidden(sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0),X4) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f365,f66])).

fof(f365,plain,
    ( ! [X4] :
        ( r2_hidden(sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0),X4)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(sK4(sK1,k10_relat_1(sK1,sK0),sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)),k10_relat_1(sK1,X4)) )
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f358,f73])).

fof(f358,plain,
    ( ! [X4] :
        ( r2_hidden(sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0),X4)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(sK4(sK1,k10_relat_1(sK1,sK0),sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)),k10_relat_1(sK1,X4)) )
    | ~ spl7_6 ),
    inference(superposition,[],[f59,f304])).

fof(f304,plain,
    ( k1_funct_1(sK1,sK4(sK1,k10_relat_1(sK1,sK0),sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0))) = sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f303])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t145_funct_1.p',d13_funct_1)).

fof(f305,plain,
    ( spl7_6
    | ~ spl7_0
    | ~ spl7_2
    | spl7_5 ),
    inference(avatar_split_clause,[],[f277,f79,f72,f65,f303])).

fof(f277,plain,
    ( k1_funct_1(sK1,sK4(sK1,k10_relat_1(sK1,sK0),sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0))) = sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f276,f73])).

fof(f276,plain,
    ( k1_funct_1(sK1,sK4(sK1,k10_relat_1(sK1,sK0),sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0))) = sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl7_0
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f271,f66])).

fof(f271,plain,
    ( k1_funct_1(sK1,sK4(sK1,k10_relat_1(sK1,sK0),sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0))) = sK2(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl7_5 ),
    inference(resolution,[],[f92,f80])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),X2)
      | k1_funct_1(X0,sK4(X0,X1,sK2(k9_relat_1(X0,X1),X2))) = sK2(k9_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f55,f37])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X1,X3)) = X3
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f33,f79])).

fof(f33,plain,(
    ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t145_funct_1.p',t145_funct_1)).

fof(f74,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f32,f72])).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------

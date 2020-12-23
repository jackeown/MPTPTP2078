%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t8_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:28 EDT 2019

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   52 (  96 expanded)
%              Number of leaves         :   11 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  168 ( 325 expanded)
%              Number of equality atoms :   27 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f150,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f63,f73,f89,f113,f135,f148,f149])).

fof(f149,plain,
    ( k1_funct_1(sK2,sK0) != sK1
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) ),
    introduced(theory_axiom,[])).

fof(f148,plain,
    ( spl7_8
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f127,f68,f83])).

fof(f83,plain,
    ( spl7_8
  <=> sP4(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f68,plain,
    ( spl7_4
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f127,plain,
    ( sP4(sK0,sK2)
    | ~ spl7_4 ),
    inference(resolution,[],[f69,f36])).

fof(f36,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t8_funct_1.p',d4_relat_1)).

fof(f69,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f135,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f133,f125])).

fof(f125,plain,
    ( k1_funct_1(sK2,sK0) != sK1
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f124,f69])).

fof(f124,plain,
    ( k1_funct_1(sK2,sK0) != sK1
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f29,f96])).

fof(f96,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_8 ),
    inference(resolution,[],[f84,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f84,plain,
    ( sP4(sK0,sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f29,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | k1_funct_1(sK2,sK0) != sK1
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t8_funct_1.p',t8_funct_1)).

fof(f133,plain,
    ( k1_funct_1(sK2,sK0) = sK1
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f132,f58])).

fof(f58,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl7_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f132,plain,
    ( ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0) = sK1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f131,f96])).

fof(f131,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0) = sK1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f126,f62])).

fof(f62,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl7_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f126,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0) = sK1
    | ~ spl7_4 ),
    inference(resolution,[],[f69,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t8_funct_1.p',d4_funct_1)).

fof(f113,plain,
    ( spl7_18
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f81,f71,f61,f57,f111])).

fof(f111,plain,
    ( spl7_18
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f71,plain,
    ( spl7_6
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f81,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f80,f58])).

fof(f80,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f75,f62])).

fof(f75,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl7_6 ),
    inference(resolution,[],[f72,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f89,plain,
    ( spl7_4
    | spl7_10 ),
    inference(avatar_split_clause,[],[f31,f87,f68])).

fof(f87,plain,
    ( spl7_10
  <=> k1_funct_1(sK2,sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f31,plain,
    ( k1_funct_1(sK2,sK0) = sK1
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,
    ( spl7_4
    | spl7_6 ),
    inference(avatar_split_clause,[],[f30,f71,f68])).

fof(f30,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f33,f61])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f32,f57])).

fof(f32,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------

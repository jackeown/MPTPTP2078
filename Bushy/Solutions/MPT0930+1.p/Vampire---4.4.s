%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t91_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:16 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   51 (  78 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :  122 ( 190 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f63,f79,f92,f100,f104,f110,f112])).

fof(f112,plain,
    ( spl9_9
    | ~ spl9_16 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f78,f106])).

fof(f106,plain,
    ( r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))
    | ~ spl9_16 ),
    inference(resolution,[],[f99,f55])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t91_mcart_1.p',d4_relat_1)).

fof(f99,plain,
    ( sP6(k1_mcart_1(sK1),sK0)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl9_16
  <=> sP6(k1_mcart_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f78,plain,
    ( ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl9_9
  <=> ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f110,plain,
    ( spl9_7
    | ~ spl9_18 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | ~ spl9_7
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f108,f75])).

fof(f75,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl9_7
  <=> ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f108,plain,
    ( r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))
    | ~ spl9_18 ),
    inference(resolution,[],[f103,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ sP3(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t91_mcart_1.p',d5_relat_1)).

fof(f103,plain,
    ( sP3(k2_mcart_1(sK1),sK0)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl9_18
  <=> sP3(k2_mcart_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f104,plain,
    ( spl9_18
    | ~ spl9_2
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f96,f90,f61,f102])).

fof(f61,plain,
    ( spl9_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f90,plain,
    ( spl9_14
  <=> k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f96,plain,
    ( sP3(k2_mcart_1(sK1),sK0)
    | ~ spl9_2
    | ~ spl9_14 ),
    inference(resolution,[],[f94,f62])).

fof(f62,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f94,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK1,X1)
        | sP3(k2_mcart_1(sK1),X1) )
    | ~ spl9_14 ),
    inference(superposition,[],[f34,f91])).

fof(f91,plain,
    ( k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1)) = sK1
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f90])).

fof(f34,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f100,plain,
    ( spl9_16
    | ~ spl9_2
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f95,f90,f61,f98])).

fof(f95,plain,
    ( sP6(k1_mcart_1(sK1),sK0)
    | ~ spl9_2
    | ~ spl9_14 ),
    inference(resolution,[],[f93,f62])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | sP6(k1_mcart_1(sK1),X0) )
    | ~ spl9_14 ),
    inference(superposition,[],[f41,f91])).

fof(f41,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f92,plain,
    ( spl9_14
    | ~ spl9_0
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f68,f61,f57,f90])).

fof(f57,plain,
    ( spl9_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f68,plain,
    ( k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1)) = sK1
    | ~ spl9_0
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f67,f58])).

fof(f58,plain,
    ( v1_relat_1(sK0)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f57])).

fof(f67,plain,
    ( ~ v1_relat_1(sK0)
    | k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1)) = sK1
    | ~ spl9_2 ),
    inference(resolution,[],[f62,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t91_mcart_1.p',t23_mcart_1)).

fof(f79,plain,
    ( ~ spl9_7
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f30,f77,f74])).

fof(f30,plain,
    ( ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))
    | ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) )
          & r2_hidden(X1,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r2_hidden(X1,X0)
           => ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
              & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t91_mcart_1.p',t91_mcart_1)).

fof(f63,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f32,f57])).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------

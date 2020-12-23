%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t19_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:58 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  46 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 (  97 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f63,f86,f120,f132])).

fof(f132,plain,(
    ~ spl9_14 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f130,f27])).

fof(f27,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
      & r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
            & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t19_relat_1.p',t19_relat_1)).

fof(f130,plain,
    ( r2_hidden(sK7(sK1,sK0),k1_relat_1(sK1))
    | ~ spl9_14 ),
    inference(resolution,[],[f119,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ sP3(X2,X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t19_relat_1.p',d4_relat_1)).

fof(f119,plain,
    ( sP3(sK7(sK1,sK0),sK1)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl9_14
  <=> sP3(sK7(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f120,plain,
    ( spl9_14
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f92,f84,f118])).

fof(f84,plain,
    ( spl9_10
  <=> r2_hidden(k4_tarski(sK7(sK1,sK0),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f92,plain,
    ( sP3(sK7(sK1,sK0),sK1)
    | ~ spl9_10 ),
    inference(resolution,[],[f85,f29])).

fof(f29,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f85,plain,
    ( r2_hidden(k4_tarski(sK7(sK1,sK0),sK0),sK1)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f86,plain,
    ( spl9_10
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f68,f61,f84])).

fof(f61,plain,
    ( spl9_2
  <=> sP6(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f68,plain,
    ( r2_hidden(k4_tarski(sK7(sK1,sK0),sK0),sK1)
    | ~ spl9_2 ),
    inference(resolution,[],[f62,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ sP6(X2,X0)
      | r2_hidden(k4_tarski(sK7(X0,X2),X2),X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t19_relat_1.p',d5_relat_1)).

fof(f62,plain,
    ( sP6(sK0,sK1)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f63,plain,
    ( spl9_2
    | ~ spl9_0 ),
    inference(avatar_split_clause,[],[f56,f51,f61])).

fof(f51,plain,
    ( spl9_0
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f56,plain,
    ( sP6(sK0,sK1)
    | ~ spl9_0 ),
    inference(resolution,[],[f52,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | sP6(X2,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f52,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f51])).

fof(f53,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f26,f51])).

fof(f26,plain,(
    r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t166_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:53 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 117 expanded)
%              Number of leaves         :   11 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  170 ( 345 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f271,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f65,f112,f119,f167,f175,f210,f222,f233,f270])).

fof(f270,plain,
    ( spl11_20
    | ~ spl11_4
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f268,f117,f63,f110])).

fof(f110,plain,
    ( spl11_20
  <=> sP8(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f63,plain,
    ( spl11_4
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f117,plain,
    ( spl11_22
  <=> r2_hidden(k4_tarski(sK0,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f268,plain,
    ( sP8(sK0,sK1,sK2)
    | ~ spl11_4
    | ~ spl11_22 ),
    inference(resolution,[],[f236,f64])).

fof(f64,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | sP8(sK0,X0,sK2) )
    | ~ spl11_22 ),
    inference(resolution,[],[f118,f37])).

fof(f37,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t166_relat_1.p',d14_relat_1)).

fof(f118,plain,
    ( r2_hidden(k4_tarski(sK0,sK3),sK2)
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f117])).

fof(f233,plain,
    ( ~ spl11_0
    | ~ spl11_20
    | ~ spl11_34
    | ~ spl11_42
    | ~ spl11_44 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_20
    | ~ spl11_34
    | ~ spl11_42
    | ~ spl11_44 ),
    inference(subsumption_resolution,[],[f231,f218])).

fof(f218,plain,
    ( ~ r2_hidden(sK9(sK2,sK1,sK0),k2_relat_1(sK2))
    | ~ spl11_0
    | ~ spl11_20
    | ~ spl11_34
    | ~ spl11_42 ),
    inference(subsumption_resolution,[],[f212,f174])).

fof(f174,plain,
    ( r2_hidden(sK9(sK2,sK1,sK0),sK1)
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl11_34
  <=> r2_hidden(sK9(sK2,sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f212,plain,
    ( ~ r2_hidden(sK9(sK2,sK1,sK0),k2_relat_1(sK2))
    | ~ r2_hidden(sK9(sK2,sK1,sK0),sK1)
    | ~ spl11_0
    | ~ spl11_20
    | ~ spl11_42 ),
    inference(resolution,[],[f209,f148])).

fof(f148,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_tarski(sK0,X3),sK2)
        | ~ r2_hidden(X3,k2_relat_1(sK2))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl11_0
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f26,f147])).

fof(f147,plain,
    ( r2_hidden(sK0,k10_relat_1(sK2,sK1))
    | ~ spl11_0
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f137,f56])).

fof(f56,plain,
    ( v1_relat_1(sK2)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl11_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f137,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK0,k10_relat_1(sK2,sK1))
    | ~ spl11_20 ),
    inference(resolution,[],[f111,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP8(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f111,plain,
    ( sP8(sK0,sK1,sK2)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f110])).

fof(f26,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK2))
      | ~ r2_hidden(k4_tarski(sK0,X3),sK2)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(sK0,k10_relat_1(sK2,sK1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <~> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X0,k10_relat_1(X2,X1))
        <=> ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t166_relat_1.p',t166_relat_1)).

fof(f209,plain,
    ( r2_hidden(k4_tarski(sK0,sK9(sK2,sK1,sK0)),sK2)
    | ~ spl11_42 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl11_42
  <=> r2_hidden(k4_tarski(sK0,sK9(sK2,sK1,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f231,plain,
    ( r2_hidden(sK9(sK2,sK1,sK0),k2_relat_1(sK2))
    | ~ spl11_44 ),
    inference(resolution,[],[f221,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ sP5(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t166_relat_1.p',d5_relat_1)).

fof(f221,plain,
    ( sP5(sK9(sK2,sK1,sK0),sK2)
    | ~ spl11_44 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl11_44
  <=> sP5(sK9(sK2,sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f222,plain,
    ( spl11_44
    | ~ spl11_42 ),
    inference(avatar_split_clause,[],[f214,f208,f220])).

fof(f214,plain,
    ( sP5(sK9(sK2,sK1,sK0),sK2)
    | ~ spl11_42 ),
    inference(resolution,[],[f209,f32])).

fof(f32,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f210,plain,
    ( spl11_42
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f135,f110,f208])).

fof(f135,plain,
    ( r2_hidden(k4_tarski(sK0,sK9(sK2,sK1,sK0)),sK2)
    | ~ spl11_20 ),
    inference(resolution,[],[f111,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | r2_hidden(k4_tarski(X3,sK9(X0,X1,X3)),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f175,plain,
    ( spl11_34
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f136,f110,f173])).

fof(f136,plain,
    ( r2_hidden(sK9(sK2,sK1,sK0),sK1)
    | ~ spl11_20 ),
    inference(resolution,[],[f111,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | r2_hidden(sK9(X0,X1,X3),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f167,plain,
    ( spl11_2
    | ~ spl11_0
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f147,f110,f55,f60])).

fof(f60,plain,
    ( spl11_2
  <=> r2_hidden(sK0,k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f119,plain,
    ( spl11_2
    | spl11_22 ),
    inference(avatar_split_clause,[],[f28,f117,f60])).

fof(f28,plain,
    ( r2_hidden(k4_tarski(sK0,sK3),sK2)
    | r2_hidden(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f112,plain,
    ( spl11_20
    | ~ spl11_0
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f90,f60,f55,f110])).

fof(f90,plain,
    ( sP8(sK0,sK1,sK2)
    | ~ spl11_0
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f86,f56])).

fof(f86,plain,
    ( sP8(sK0,sK1,sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl11_2 ),
    inference(resolution,[],[f61,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k10_relat_1(X0,X1))
      | sP8(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP8(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,
    ( r2_hidden(sK0,k10_relat_1(sK2,sK1))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f65,plain,
    ( spl11_2
    | spl11_4 ),
    inference(avatar_split_clause,[],[f29,f63,f60])).

fof(f29,plain,
    ( r2_hidden(sK3,sK1)
    | r2_hidden(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f30,f55])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------

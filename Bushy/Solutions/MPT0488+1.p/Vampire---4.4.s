%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t86_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:05 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 166 expanded)
%              Number of leaves         :   16 (  68 expanded)
%              Depth                    :    8
%              Number of atoms          :  222 ( 437 expanded)
%              Number of equality atoms :    7 (  24 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f382,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f69,f78,f105,f138,f170,f189,f252,f269,f277,f291,f307,f354,f369,f381])).

fof(f381,plain,
    ( spl10_14
    | ~ spl10_56 ),
    inference(avatar_split_clause,[],[f375,f367,f103])).

fof(f103,plain,
    ( spl10_14
  <=> sP4(sK0,k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f367,plain,
    ( spl10_56
  <=> r2_hidden(k4_tarski(sK0,sK5(sK2,sK0)),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f375,plain,
    ( sP4(sK0,k7_relat_1(sK2,sK1))
    | ~ spl10_56 ),
    inference(resolution,[],[f368,f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/relat_1__t86_relat_1.p',d4_relat_1)).

fof(f368,plain,
    ( r2_hidden(k4_tarski(sK0,sK5(sK2,sK0)),k7_relat_1(sK2,sK1))
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f367])).

fof(f369,plain,
    ( spl10_56
    | ~ spl10_0
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f359,f352,f56,f367])).

fof(f56,plain,
    ( spl10_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f352,plain,
    ( spl10_54
  <=> sP8(sK5(sK2,sK0),sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f359,plain,
    ( r2_hidden(k4_tarski(sK0,sK5(sK2,sK0)),k7_relat_1(sK2,sK1))
    | ~ spl10_0
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f358,f57])).

fof(f57,plain,
    ( v1_relat_1(sK2)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f56])).

fof(f358,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,sK5(sK2,sK0)),k7_relat_1(sK2,sK1))
    | ~ spl10_0
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f357,f60])).

fof(f60,plain,
    ( ! [X2] : v1_relat_1(k7_relat_1(sK2,X2))
    | ~ spl10_0 ),
    inference(resolution,[],[f57,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t86_relat_1.p',dt_k7_relat_1)).

fof(f357,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,sK5(sK2,sK0)),k7_relat_1(sK2,sK1))
    | ~ spl10_54 ),
    inference(resolution,[],[f353,f54])).

fof(f54,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP8(X4,X3,X1,X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ sP8(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t86_relat_1.p',d11_relat_1)).

fof(f353,plain,
    ( sP8(sK5(sK2,sK0),sK0,sK1,sK2)
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f352])).

fof(f354,plain,
    ( spl10_54
    | ~ spl10_4
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f345,f168,f67,f352])).

fof(f67,plain,
    ( spl10_4
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f168,plain,
    ( spl10_30
  <=> r2_hidden(k4_tarski(sK0,sK5(sK2,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f345,plain,
    ( sP8(sK5(sK2,sK0),sK0,sK1,sK2)
    | ~ spl10_4
    | ~ spl10_30 ),
    inference(resolution,[],[f169,f279])).

fof(f279,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK0,X0),X1)
        | sP8(X0,sK0,sK1,X1) )
    | ~ spl10_4 ),
    inference(resolution,[],[f68,f40])).

fof(f40,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | sP8(X4,X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f169,plain,
    ( r2_hidden(k4_tarski(sK0,sK5(sK2,sK0)),sK2)
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f168])).

fof(f307,plain,
    ( spl10_20
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f298,f289,f136])).

fof(f136,plain,
    ( spl10_20
  <=> sP4(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f289,plain,
    ( spl10_48
  <=> r2_hidden(k4_tarski(sK0,sK5(k7_relat_1(sK2,sK1),sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f298,plain,
    ( sP4(sK0,sK2)
    | ~ spl10_48 ),
    inference(resolution,[],[f290,f34])).

fof(f290,plain,
    ( r2_hidden(k4_tarski(sK0,sK5(k7_relat_1(sK2,sK1),sK0)),sK2)
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f289])).

fof(f291,plain,
    ( spl10_48
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f254,f250,f289])).

fof(f250,plain,
    ( spl10_44
  <=> sP8(sK5(k7_relat_1(sK2,sK1),sK0),sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f254,plain,
    ( r2_hidden(k4_tarski(sK0,sK5(k7_relat_1(sK2,sK1),sK0)),sK2)
    | ~ spl10_44 ),
    inference(resolution,[],[f251,f42])).

fof(f42,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP8(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f251,plain,
    ( sP8(sK5(k7_relat_1(sK2,sK1),sK0),sK0,sK1,sK2)
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f250])).

fof(f277,plain,
    ( spl10_4
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f253,f250,f67])).

fof(f253,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl10_44 ),
    inference(resolution,[],[f251,f41])).

fof(f41,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP8(X4,X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f269,plain,
    ( ~ spl10_4
    | ~ spl10_14
    | ~ spl10_20 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_14
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f144,f116])).

fof(f116,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl10_4
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f70,f111])).

fof(f111,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl10_14 ),
    inference(resolution,[],[f104,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f104,plain,
    ( sP4(sK0,k7_relat_1(sK2,sK1))
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f103])).

fof(f70,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f27,f68])).

fof(f27,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <~> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
        <=> ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t86_relat_1.p',t86_relat_1)).

fof(f144,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl10_20 ),
    inference(resolution,[],[f137,f52])).

fof(f137,plain,
    ( sP4(sK0,sK2)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f136])).

fof(f252,plain,
    ( spl10_44
    | ~ spl10_0
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f199,f187,f56,f250])).

fof(f187,plain,
    ( spl10_34
  <=> r2_hidden(k4_tarski(sK0,sK5(k7_relat_1(sK2,sK1),sK0)),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f199,plain,
    ( sP8(sK5(k7_relat_1(sK2,sK1),sK0),sK0,sK1,sK2)
    | ~ spl10_0
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f198,f57])).

fof(f198,plain,
    ( sP8(sK5(k7_relat_1(sK2,sK1),sK0),sK0,sK1,sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl10_0
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f192,f60])).

fof(f192,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | sP8(sK5(k7_relat_1(sK2,sK1),sK0),sK0,sK1,sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl10_34 ),
    inference(resolution,[],[f188,f53])).

fof(f53,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | sP8(X4,X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | sP8(X4,X3,X1,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f188,plain,
    ( r2_hidden(k4_tarski(sK0,sK5(k7_relat_1(sK2,sK1),sK0)),k7_relat_1(sK2,sK1))
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f187])).

fof(f189,plain,
    ( spl10_34
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f110,f103,f187])).

fof(f110,plain,
    ( r2_hidden(k4_tarski(sK0,sK5(k7_relat_1(sK2,sK1),sK0)),k7_relat_1(sK2,sK1))
    | ~ spl10_14 ),
    inference(resolution,[],[f104,f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f170,plain,
    ( spl10_30
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f143,f136,f168])).

fof(f143,plain,
    ( r2_hidden(k4_tarski(sK0,sK5(sK2,sK0)),sK2)
    | ~ spl10_20 ),
    inference(resolution,[],[f137,f33])).

fof(f138,plain,
    ( spl10_20
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f130,f76,f136])).

fof(f76,plain,
    ( spl10_6
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f130,plain,
    ( sP4(sK0,sK2)
    | ~ spl10_6 ),
    inference(resolution,[],[f77,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | sP4(X2,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f77,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f105,plain,
    ( spl10_14
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f92,f64,f103])).

fof(f64,plain,
    ( spl10_2
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f92,plain,
    ( sP4(sK0,k7_relat_1(sK2,sK1))
    | ~ spl10_2 ),
    inference(resolution,[],[f65,f51])).

fof(f65,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f78,plain,
    ( spl10_2
    | spl10_6 ),
    inference(avatar_split_clause,[],[f29,f76,f64])).

fof(f29,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,
    ( spl10_2
    | spl10_4 ),
    inference(avatar_split_clause,[],[f28,f67,f64])).

fof(f28,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    spl10_0 ),
    inference(avatar_split_clause,[],[f30,f56])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 232 expanded)
%              Number of leaves         :   12 (  73 expanded)
%              Depth                    :   24
%              Number of atoms          :  304 ( 673 expanded)
%              Number of equality atoms :   92 ( 277 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f66,f74,f80,f88,f249])).

fof(f249,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_5
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_5
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f44,f49,f65,f229,f35])).

fof(f35,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f229,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK1))
    | spl6_5
    | ~ spl6_7 ),
    inference(condensation,[],[f228])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | spl6_5
    | ~ spl6_7 ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | spl6_5
    | ~ spl6_7 ),
    inference(superposition,[],[f218,f183])).

fof(f183,plain,
    ( ! [X6,X7] :
        ( sK5(X6,k2_relat_1(sK1)) = X7
        | ~ r2_hidden(X6,k2_relat_1(sK1))
        | ~ r2_hidden(X7,k2_relat_1(sK1)) )
    | spl6_5
    | ~ spl6_7 ),
    inference(trivial_inequality_removal,[],[f182])).

fof(f182,plain,
    ( ! [X6,X7] :
        ( k2_relat_1(sK1) != k2_relat_1(sK1)
        | ~ r2_hidden(X6,k2_relat_1(sK1))
        | sK5(X6,k2_relat_1(sK1)) = X7
        | ~ r2_hidden(X7,k2_relat_1(sK1)) )
    | spl6_5
    | ~ spl6_7 ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,
    ( ! [X6,X7] :
        ( k2_relat_1(sK1) != k2_relat_1(sK1)
        | ~ r2_hidden(X6,k2_relat_1(sK1))
        | ~ r2_hidden(X6,k2_relat_1(sK1))
        | sK5(X6,k2_relat_1(sK1)) = X7
        | ~ r2_hidden(X7,k2_relat_1(sK1)) )
    | spl6_5
    | ~ spl6_7 ),
    inference(resolution,[],[f169,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK1))
        | X0 = X1
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl6_7 ),
    inference(superposition,[],[f87,f87])).

fof(f87,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK0) = X1
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_7
  <=> ! [X1] :
        ( k1_funct_1(sK1,sK0) = X1
        | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(X0,X1),X1)
        | k2_relat_1(sK1) != X1
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | spl6_5
    | ~ spl6_7 ),
    inference(superposition,[],[f164,f87])).

fof(f164,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k1_funct_1(sK1,sK0),X0),X0)
        | k2_relat_1(sK1) != X0
        | ~ r2_hidden(k1_funct_1(sK1,sK0),X0) )
    | spl6_5 ),
    inference(trivial_inequality_removal,[],[f163])).

fof(f163,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0)
        | ~ r2_hidden(k1_funct_1(sK1,sK0),X0)
        | k2_relat_1(sK1) != X0
        | r2_hidden(sK5(k1_funct_1(sK1,sK0),X0),X0) )
    | spl6_5 ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0)
        | ~ r2_hidden(k1_funct_1(sK1,sK0),X0)
        | k2_relat_1(sK1) != X0
        | r2_hidden(sK5(k1_funct_1(sK1,sK0),X0),X0)
        | k2_relat_1(sK1) != X0 )
    | spl6_5 ),
    inference(superposition,[],[f76,f75])).

fof(f75,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),X0)
        | r2_hidden(sK5(k1_funct_1(sK1,sK0),X0),X0)
        | k2_relat_1(sK1) != X0 )
    | spl6_5 ),
    inference(superposition,[],[f73,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = X1
      | r2_hidden(sK5(X0,X1),X1)
      | sK5(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f25,f27])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f15,f22])).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f15,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) = X0
      | r2_hidden(sK5(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f73,plain,
    ( k2_relat_1(sK1) != k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_5
  <=> k2_relat_1(sK1) = k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f76,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK0) != sK5(k1_funct_1(sK1,sK0),X1)
        | ~ r2_hidden(sK5(k1_funct_1(sK1,sK0),X1),X1)
        | k2_relat_1(sK1) != X1 )
    | spl6_5 ),
    inference(superposition,[],[f73,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = X1
      | ~ r2_hidden(sK5(X0,X1),X1)
      | sK5(X0,X1) != X0 ) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X0
      | ~ r2_hidden(sK5(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(X0,k2_relat_1(sK1)),k2_relat_1(sK1))
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | spl6_5
    | ~ spl6_7 ),
    inference(equality_resolution,[],[f214])).

fof(f214,plain,
    ( ! [X6,X5] :
        ( sK5(X6,k2_relat_1(sK1)) != X5
        | ~ r2_hidden(X5,k2_relat_1(sK1))
        | ~ r2_hidden(X6,k2_relat_1(sK1)) )
    | spl6_5
    | ~ spl6_7 ),
    inference(trivial_inequality_removal,[],[f213])).

fof(f213,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X5,k2_relat_1(sK1))
        | sK5(X6,k2_relat_1(sK1)) != X5
        | k2_relat_1(sK1) != k2_relat_1(sK1)
        | ~ r2_hidden(X6,k2_relat_1(sK1)) )
    | spl6_5
    | ~ spl6_7 ),
    inference(duplicate_literal_removal,[],[f210])).

fof(f210,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X5,k2_relat_1(sK1))
        | sK5(X6,k2_relat_1(sK1)) != X5
        | k2_relat_1(sK1) != k2_relat_1(sK1)
        | ~ r2_hidden(X6,k2_relat_1(sK1))
        | ~ r2_hidden(X6,k2_relat_1(sK1)) )
    | spl6_5
    | ~ spl6_7 ),
    inference(resolution,[],[f197,f169])).

fof(f197,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(X8,k2_relat_1(sK1))
        | ~ r2_hidden(X7,k2_relat_1(sK1))
        | X7 != X8 )
    | spl6_5
    | ~ spl6_7 ),
    inference(trivial_inequality_removal,[],[f196])).

fof(f196,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(X8,k2_relat_1(sK1))
        | ~ r2_hidden(X7,k2_relat_1(sK1))
        | k2_relat_1(sK1) != k2_relat_1(sK1)
        | X7 != X8 )
    | spl6_5
    | ~ spl6_7 ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(X8,k2_relat_1(sK1))
        | ~ r2_hidden(X7,k2_relat_1(sK1))
        | k2_relat_1(sK1) != k2_relat_1(sK1)
        | X7 != X8
        | ~ r2_hidden(X7,k2_relat_1(sK1))
        | ~ r2_hidden(X8,k2_relat_1(sK1)) )
    | spl6_5
    | ~ spl6_7 ),
    inference(superposition,[],[f94,f183])).

fof(f94,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK5(X2,X3),X3)
        | ~ r2_hidden(X2,k2_relat_1(sK1))
        | k2_relat_1(sK1) != X3
        | sK5(X2,X3) != X2 )
    | spl6_5
    | ~ spl6_7 ),
    inference(superposition,[],[f90,f30])).

fof(f90,plain,
    ( ! [X0] :
        ( k2_relat_1(sK1) != k1_enumset1(X0,X0,X0)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | spl6_5
    | ~ spl6_7 ),
    inference(superposition,[],[f73,f87])).

fof(f65,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_4
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f49,plain,
    ( v1_funct_1(sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl6_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f44,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl6_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f88,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_7
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f83,f78,f86,f47,f42])).

fof(f78,plain,
    ( spl6_6
  <=> ! [X0] :
        ( sK0 = sK3(sK1,X0)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f83,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK0) = X1
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl6_6 ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK0) = X1
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl6_6 ),
    inference(superposition,[],[f36,f79])).

fof(f79,plain,
    ( ! [X0] :
        ( sK0 = sK3(sK1,X0)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f36,plain,(
    ! [X2,X0] :
      ( k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f80,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_6
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f68,f52,f78,f47,f42])).

fof(f52,plain,
    ( spl6_3
  <=> k1_relat_1(sK1) = k1_enumset1(sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f68,plain,
    ( ! [X0] :
        ( sK0 = sK3(sK1,X0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f59,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f59,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | sK0 = X0 )
    | ~ spl6_3 ),
    inference(superposition,[],[f38,f54])).

fof(f54,plain,
    ( k1_relat_1(sK1) = k1_enumset1(sK0,sK0,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_enumset1(X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f24,f27])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f74,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f28,f71])).

fof(f28,plain,(
    k2_relat_1(sK1) != k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f14,f27])).

fof(f14,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f66,plain,
    ( spl6_4
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f58,f52,f63])).

fof(f58,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl6_3 ),
    inference(superposition,[],[f40,f54])).

fof(f40,plain,(
    ! [X2] : r2_hidden(X2,k1_enumset1(X2,X2,X2)) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_enumset1(X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f23,f27])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f55,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f29,f52])).

fof(f29,plain,(
    k1_relat_1(sK1) = k1_enumset1(sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f13,f27])).

fof(f13,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f50,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f12,f47])).

fof(f12,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f45,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f11,f42])).

fof(f11,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n005.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:58:32 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.22/0.51  % (2583)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.51  % (2574)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (2586)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (2591)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (2600)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.52  % (2570)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (2585)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (2576)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (2577)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (2572)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (2594)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (2600)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f250,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f45,f50,f55,f66,f74,f80,f88,f249])).
% 0.22/0.53  fof(f249,plain,(
% 0.22/0.53    ~spl6_1 | ~spl6_2 | ~spl6_4 | spl6_5 | ~spl6_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f238])).
% 0.22/0.53  fof(f238,plain,(
% 0.22/0.53    $false | (~spl6_1 | ~spl6_2 | ~spl6_4 | spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f44,f49,f65,f229,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0,X3] : (r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.53    inference(equality_resolution,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.53  fof(f229,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1))) ) | (spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(condensation,[],[f228])).
% 0.22/0.53  fof(f228,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f227])).
% 0.22/0.53  fof(f227,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | ~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | (spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(superposition,[],[f218,f183])).
% 0.22/0.53  fof(f183,plain,(
% 0.22/0.53    ( ! [X6,X7] : (sK5(X6,k2_relat_1(sK1)) = X7 | ~r2_hidden(X6,k2_relat_1(sK1)) | ~r2_hidden(X7,k2_relat_1(sK1))) ) | (spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f182])).
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    ( ! [X6,X7] : (k2_relat_1(sK1) != k2_relat_1(sK1) | ~r2_hidden(X6,k2_relat_1(sK1)) | sK5(X6,k2_relat_1(sK1)) = X7 | ~r2_hidden(X7,k2_relat_1(sK1))) ) | (spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f179])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    ( ! [X6,X7] : (k2_relat_1(sK1) != k2_relat_1(sK1) | ~r2_hidden(X6,k2_relat_1(sK1)) | ~r2_hidden(X6,k2_relat_1(sK1)) | sK5(X6,k2_relat_1(sK1)) = X7 | ~r2_hidden(X7,k2_relat_1(sK1))) ) | (spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(resolution,[],[f169,f89])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | X0 = X1 | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl6_7),
% 0.22/0.53    inference(superposition,[],[f87,f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ( ! [X1] : (k1_funct_1(sK1,sK0) = X1 | ~r2_hidden(X1,k2_relat_1(sK1))) ) | ~spl6_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    spl6_7 <=> ! [X1] : (k1_funct_1(sK1,sK0) = X1 | ~r2_hidden(X1,k2_relat_1(sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | k2_relat_1(sK1) != X1 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(superposition,[],[f164,f87])).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK5(k1_funct_1(sK1,sK0),X0),X0) | k2_relat_1(sK1) != X0 | ~r2_hidden(k1_funct_1(sK1,sK0),X0)) ) | spl6_5),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f163])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    ( ! [X0] : (k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0) | ~r2_hidden(k1_funct_1(sK1,sK0),X0) | k2_relat_1(sK1) != X0 | r2_hidden(sK5(k1_funct_1(sK1,sK0),X0),X0)) ) | spl6_5),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f162])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    ( ! [X0] : (k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0) | ~r2_hidden(k1_funct_1(sK1,sK0),X0) | k2_relat_1(sK1) != X0 | r2_hidden(sK5(k1_funct_1(sK1,sK0),X0),X0) | k2_relat_1(sK1) != X0) ) | spl6_5),
% 0.22/0.53    inference(superposition,[],[f76,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X0] : (k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),X0) | r2_hidden(sK5(k1_funct_1(sK1,sK0),X0),X0) | k2_relat_1(sK1) != X0) ) | spl6_5),
% 0.22/0.53    inference(superposition,[],[f73,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = X1 | r2_hidden(sK5(X0,X1),X1) | sK5(X0,X1) = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f25,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f15,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    k2_relat_1(sK1) != k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | spl6_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl6_5 <=> k2_relat_1(sK1) = k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X1] : (k1_funct_1(sK1,sK0) != sK5(k1_funct_1(sK1,sK0),X1) | ~r2_hidden(sK5(k1_funct_1(sK1,sK0),X1),X1) | k2_relat_1(sK1) != X1) ) | spl6_5),
% 0.22/0.53    inference(superposition,[],[f73,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = X1 | ~r2_hidden(sK5(X0,X1),X1) | sK5(X0,X1) != X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f26,f27])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f218,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK5(X0,k2_relat_1(sK1)),k2_relat_1(sK1)) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(equality_resolution,[],[f214])).
% 0.22/0.53  fof(f214,plain,(
% 0.22/0.53    ( ! [X6,X5] : (sK5(X6,k2_relat_1(sK1)) != X5 | ~r2_hidden(X5,k2_relat_1(sK1)) | ~r2_hidden(X6,k2_relat_1(sK1))) ) | (spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f213])).
% 0.22/0.53  fof(f213,plain,(
% 0.22/0.53    ( ! [X6,X5] : (~r2_hidden(X5,k2_relat_1(sK1)) | sK5(X6,k2_relat_1(sK1)) != X5 | k2_relat_1(sK1) != k2_relat_1(sK1) | ~r2_hidden(X6,k2_relat_1(sK1))) ) | (spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f210])).
% 0.22/0.53  fof(f210,plain,(
% 0.22/0.53    ( ! [X6,X5] : (~r2_hidden(X5,k2_relat_1(sK1)) | sK5(X6,k2_relat_1(sK1)) != X5 | k2_relat_1(sK1) != k2_relat_1(sK1) | ~r2_hidden(X6,k2_relat_1(sK1)) | ~r2_hidden(X6,k2_relat_1(sK1))) ) | (spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(resolution,[],[f197,f169])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    ( ! [X8,X7] : (~r2_hidden(X8,k2_relat_1(sK1)) | ~r2_hidden(X7,k2_relat_1(sK1)) | X7 != X8) ) | (spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f196])).
% 0.22/0.53  fof(f196,plain,(
% 0.22/0.53    ( ! [X8,X7] : (~r2_hidden(X8,k2_relat_1(sK1)) | ~r2_hidden(X7,k2_relat_1(sK1)) | k2_relat_1(sK1) != k2_relat_1(sK1) | X7 != X8) ) | (spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f193])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    ( ! [X8,X7] : (~r2_hidden(X8,k2_relat_1(sK1)) | ~r2_hidden(X7,k2_relat_1(sK1)) | k2_relat_1(sK1) != k2_relat_1(sK1) | X7 != X8 | ~r2_hidden(X7,k2_relat_1(sK1)) | ~r2_hidden(X8,k2_relat_1(sK1))) ) | (spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(superposition,[],[f94,f183])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~r2_hidden(sK5(X2,X3),X3) | ~r2_hidden(X2,k2_relat_1(sK1)) | k2_relat_1(sK1) != X3 | sK5(X2,X3) != X2) ) | (spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(superposition,[],[f90,f30])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ( ! [X0] : (k2_relat_1(sK1) != k1_enumset1(X0,X0,X0) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (spl6_5 | ~spl6_7)),
% 0.22/0.53    inference(superposition,[],[f73,f87])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl6_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    spl6_4 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    v1_funct_1(sK1) | ~spl6_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    spl6_2 <=> v1_funct_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    v1_relat_1(sK1) | ~spl6_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    spl6_1 <=> v1_relat_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ~spl6_1 | ~spl6_2 | spl6_7 | ~spl6_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f83,f78,f86,f47,f42])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    spl6_6 <=> ! [X0] : (sK0 = sK3(sK1,X0) | ~r2_hidden(X0,k2_relat_1(sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ( ! [X1] : (k1_funct_1(sK1,sK0) = X1 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | ~spl6_6),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X1] : (k1_funct_1(sK1,sK0) = X1 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | ~spl6_6),
% 0.22/0.53    inference(superposition,[],[f36,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X0] : (sK0 = sK3(sK1,X0) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl6_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f78])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X2,X0] : (k1_funct_1(X0,sK3(X0,X2)) = X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.53    inference(equality_resolution,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ~spl6_1 | ~spl6_2 | spl6_6 | ~spl6_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f68,f52,f78,f47,f42])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    spl6_3 <=> k1_relat_1(sK1) = k1_enumset1(sK0,sK0,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X0] : (sK0 = sK3(sK1,X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl6_3),
% 0.22/0.53    inference(resolution,[],[f59,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X2,X0] : (r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.53    inference(equality_resolution,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | sK0 = X0) ) | ~spl6_3),
% 0.22/0.53    inference(superposition,[],[f38,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    k1_relat_1(sK1) = k1_enumset1(sK0,sK0,sK0) | ~spl6_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f52])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~r2_hidden(X2,k1_enumset1(X0,X0,X0)) | X0 = X2) )),
% 0.22/0.53    inference(equality_resolution,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.22/0.53    inference(definition_unfolding,[],[f24,f27])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ~spl6_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f28,f71])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    k2_relat_1(sK1) != k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.22/0.53    inference(definition_unfolding,[],[f14,f27])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f7])).
% 0.22/0.53  fof(f7,plain,(
% 0.22/0.53    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.53    inference(negated_conjecture,[],[f5])).
% 0.22/0.53  fof(f5,conjecture,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    spl6_4 | ~spl6_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f58,f52,f63])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl6_3),
% 0.22/0.53    inference(superposition,[],[f40,f54])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X2] : (r2_hidden(X2,k1_enumset1(X2,X2,X2))) )),
% 0.22/0.53    inference(equality_resolution,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_enumset1(X2,X2,X2) != X1) )),
% 0.22/0.53    inference(equality_resolution,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.22/0.53    inference(definition_unfolding,[],[f23,f27])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    spl6_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f29,f52])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    k1_relat_1(sK1) = k1_enumset1(sK0,sK0,sK0)),
% 0.22/0.53    inference(definition_unfolding,[],[f13,f27])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    spl6_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f12,f47])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    v1_funct_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    spl6_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f11,f42])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    v1_relat_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (2600)------------------------------
% 0.22/0.53  % (2600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2600)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (2600)Memory used [KB]: 10746
% 0.22/0.53  % (2600)Time elapsed: 0.122 s
% 0.22/0.53  % (2600)------------------------------
% 0.22/0.53  % (2600)------------------------------
% 0.22/0.53  % (2593)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (2567)Success in time 0.174 s
%------------------------------------------------------------------------------

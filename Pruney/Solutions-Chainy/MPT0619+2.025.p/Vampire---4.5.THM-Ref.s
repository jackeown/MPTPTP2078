%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 199 expanded)
%              Number of leaves         :   20 (  67 expanded)
%              Depth                    :   19
%              Number of atoms          :  372 ( 736 expanded)
%              Number of equality atoms :  139 ( 339 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f80,f85,f91,f106,f116,f135,f183,f253])).

fof(f253,plain,
    ( spl3_4
    | ~ spl3_8
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl3_4
    | ~ spl3_8
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f182,f84,f227])).

fof(f227,plain,
    ( ! [X1] :
        ( k2_relat_1(sK1) = k2_enumset1(X1,X1,X1,X1)
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | spl3_4
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f226])).

fof(f226,plain,
    ( ! [X1] :
        ( X1 != X1
        | k2_relat_1(sK1) = k2_enumset1(X1,X1,X1,X1)
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | spl3_4
    | ~ spl3_8 ),
    inference(duplicate_literal_removal,[],[f222])).

fof(f222,plain,
    ( ! [X1] :
        ( X1 != X1
        | k2_relat_1(sK1) = k2_enumset1(X1,X1,X1,X1)
        | ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | spl3_4
    | ~ spl3_8 ),
    inference(superposition,[],[f53,f219])).

fof(f219,plain,
    ( ! [X0] :
        ( sK2(X0,X0,k2_relat_1(sK1)) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | spl3_4
    | ~ spl3_8 ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | sK2(X0,X0,k2_relat_1(sK1)) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | spl3_4
    | ~ spl3_8 ),
    inference(equality_resolution,[],[f213])).

fof(f213,plain,
    ( ! [X0,X1] :
        ( X0 != X1
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | sK2(X0,X0,k2_relat_1(sK1)) = X0
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | spl3_4
    | ~ spl3_8 ),
    inference(equality_factoring,[],[f207])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( sK2(X0,X0,k2_relat_1(sK1)) = X1
        | ~ r2_hidden(X0,k2_relat_1(sK1))
        | sK2(X0,X0,k2_relat_1(sK1)) = X0
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | spl3_4
    | ~ spl3_8 ),
    inference(resolution,[],[f205,f136])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK1))
        | X0 = X1
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl3_8 ),
    inference(superposition,[],[f134,f134])).

fof(f134,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK0) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl3_8
  <=> ! [X0] :
        ( k1_funct_1(sK1,sK0) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f205,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0,X0,k2_relat_1(sK1)),k2_relat_1(sK1))
        | sK2(X0,X0,k2_relat_1(sK1)) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | spl3_4
    | ~ spl3_8 ),
    inference(equality_resolution,[],[f194])).

fof(f194,plain,
    ( ! [X12,X13] :
        ( k2_relat_1(sK1) != X13
        | ~ r2_hidden(X12,k2_relat_1(sK1))
        | sK2(X12,X12,X13) = X12
        | r2_hidden(sK2(X12,X12,X13),X13) )
    | spl3_4
    | ~ spl3_8 ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,
    ( ! [X12,X13] :
        ( k2_relat_1(sK1) != X13
        | ~ r2_hidden(X12,k2_relat_1(sK1))
        | sK2(X12,X12,X13) = X12
        | sK2(X12,X12,X13) = X12
        | r2_hidden(sK2(X12,X12,X13),X13) )
    | spl3_4
    | ~ spl3_8 ),
    inference(superposition,[],[f137,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X0,X0,X0,X1) = X2
      | sK2(X0,X1,X2) = X1
      | sK2(X0,X1,X2) = X0
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f40,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK2(X0,X1,X2) = X1
      | sK2(X0,X1,X2) = X0
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f137,plain,
    ( ! [X0] :
        ( k2_relat_1(sK1) != k2_enumset1(X0,X0,X0,X0)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | spl3_4
    | ~ spl3_8 ),
    inference(superposition,[],[f84,f134])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) != X1
      | k2_enumset1(X0,X0,X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK2(X0,X1,X2) != X1
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,
    ( k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_4
  <=> k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f182,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl3_17
  <=> r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f183,plain,
    ( ~ spl3_5
    | ~ spl3_1
    | ~ spl3_2
    | spl3_17
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f176,f103,f180,f72,f67,f88])).

fof(f88,plain,
    ( spl3_5
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f67,plain,
    ( spl3_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f72,plain,
    ( spl3_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f103,plain,
    ( spl3_6
  <=> k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f176,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl3_6 ),
    inference(superposition,[],[f129,f105])).

fof(f105,plain,
    ( k2_relat_1(sK1) = k11_relat_1(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f129,plain,(
    ! [X4,X5] :
      ( r2_hidden(k1_funct_1(X5,X4),k11_relat_1(X5,X4))
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5)
      | ~ r2_hidden(X4,k1_relat_1(X5)) ) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_relat_1(X5))
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5)
      | r2_hidden(k1_funct_1(X5,X4),k11_relat_1(X5,X4))
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f60,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f60,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

% (19676)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f135,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_8
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f120,f114,f133,f72,f67])).

fof(f114,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | r2_hidden(k4_tarski(sK0,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f120,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK0) = X0
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl3_7 ),
    inference(resolution,[],[f34,f115])).

fof(f115,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK0,X0),sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f116,plain,
    ( ~ spl3_1
    | spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f107,f103,f114,f67])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | r2_hidden(k4_tarski(sK0,X0),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_6 ),
    inference(superposition,[],[f46,f105])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f106,plain,
    ( ~ spl3_1
    | spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f100,f77,f103,f67])).

% (19681)Refutation not found, incomplete strategy% (19681)------------------------------
% (19681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f77,plain,
    ( spl3_3
  <=> k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

% (19681)Termination reason: Refutation not found, incomplete strategy

% (19681)Memory used [KB]: 1663
% (19681)Time elapsed: 0.142 s
fof(f100,plain,
    ( k2_relat_1(sK1) = k11_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl3_3 ),
    inference(duplicate_literal_removal,[],[f99])).

% (19681)------------------------------
% (19681)------------------------------
fof(f99,plain,
    ( k2_relat_1(sK1) = k11_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_3 ),
    inference(superposition,[],[f36,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( k11_relat_1(X0,sK0) = k9_relat_1(X0,k1_relat_1(sK1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_3 ),
    inference(superposition,[],[f59,f79])).

fof(f79,plain,
    ( k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f36,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f91,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f86,f77,f88])).

fof(f86,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl3_3 ),
    inference(superposition,[],[f62,f79])).

fof(f62,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f56])).

% (19661)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f51,f82])).

fof(f51,plain,(
    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f32,f50])).

fof(f32,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
      & k1_tarski(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f80,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f52,f77])).

fof(f52,plain,(
    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f31,f50])).

fof(f31,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f72])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f29,f67])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (19657)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (19674)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.50  % (19658)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (19663)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (19666)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (19675)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (19667)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (19652)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (19662)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (19678)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (19681)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (19679)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (19671)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (19656)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (19669)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (19654)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (19653)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (19659)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (19668)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (19668)Refutation not found, incomplete strategy% (19668)------------------------------
% 0.20/0.53  % (19668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19668)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (19668)Memory used [KB]: 10618
% 0.20/0.53  % (19668)Time elapsed: 0.128 s
% 0.20/0.53  % (19668)------------------------------
% 0.20/0.53  % (19668)------------------------------
% 0.20/0.53  % (19665)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (19670)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (19675)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f254,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f70,f75,f80,f85,f91,f106,f116,f135,f183,f253])).
% 0.20/0.53  fof(f253,plain,(
% 0.20/0.53    spl3_4 | ~spl3_8 | ~spl3_17),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f238])).
% 0.20/0.53  fof(f238,plain,(
% 0.20/0.53    $false | (spl3_4 | ~spl3_8 | ~spl3_17)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f182,f84,f227])).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    ( ! [X1] : (k2_relat_1(sK1) = k2_enumset1(X1,X1,X1,X1) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | (spl3_4 | ~spl3_8)),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f226])).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    ( ! [X1] : (X1 != X1 | k2_relat_1(sK1) = k2_enumset1(X1,X1,X1,X1) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | (spl3_4 | ~spl3_8)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f222])).
% 0.20/0.53  fof(f222,plain,(
% 0.20/0.53    ( ! [X1] : (X1 != X1 | k2_relat_1(sK1) = k2_enumset1(X1,X1,X1,X1) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | (spl3_4 | ~spl3_8)),
% 0.20/0.53    inference(superposition,[],[f53,f219])).
% 0.20/0.53  fof(f219,plain,(
% 0.20/0.53    ( ! [X0] : (sK2(X0,X0,k2_relat_1(sK1)) = X0 | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (spl3_4 | ~spl3_8)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f218])).
% 0.20/0.53  fof(f218,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | sK2(X0,X0,k2_relat_1(sK1)) = X0 | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (spl3_4 | ~spl3_8)),
% 0.20/0.53    inference(equality_resolution,[],[f213])).
% 0.20/0.53  fof(f213,plain,(
% 0.20/0.53    ( ! [X0,X1] : (X0 != X1 | ~r2_hidden(X0,k2_relat_1(sK1)) | sK2(X0,X0,k2_relat_1(sK1)) = X0 | ~r2_hidden(X1,k2_relat_1(sK1))) ) | (spl3_4 | ~spl3_8)),
% 0.20/0.53    inference(equality_factoring,[],[f207])).
% 0.20/0.53  fof(f207,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sK2(X0,X0,k2_relat_1(sK1)) = X1 | ~r2_hidden(X0,k2_relat_1(sK1)) | sK2(X0,X0,k2_relat_1(sK1)) = X0 | ~r2_hidden(X1,k2_relat_1(sK1))) ) | (spl3_4 | ~spl3_8)),
% 0.20/0.53    inference(resolution,[],[f205,f136])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | X0 = X1 | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl3_8),
% 0.20/0.53    inference(superposition,[],[f134,f134])).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    ( ! [X0] : (k1_funct_1(sK1,sK0) = X0 | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl3_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f133])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    spl3_8 <=> ! [X0] : (k1_funct_1(sK1,sK0) = X0 | ~r2_hidden(X0,k2_relat_1(sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.53  fof(f205,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK2(X0,X0,k2_relat_1(sK1)),k2_relat_1(sK1)) | sK2(X0,X0,k2_relat_1(sK1)) = X0 | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (spl3_4 | ~spl3_8)),
% 0.20/0.53    inference(equality_resolution,[],[f194])).
% 0.20/0.53  fof(f194,plain,(
% 0.20/0.53    ( ! [X12,X13] : (k2_relat_1(sK1) != X13 | ~r2_hidden(X12,k2_relat_1(sK1)) | sK2(X12,X12,X13) = X12 | r2_hidden(sK2(X12,X12,X13),X13)) ) | (spl3_4 | ~spl3_8)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f191])).
% 0.20/0.53  fof(f191,plain,(
% 0.20/0.53    ( ! [X12,X13] : (k2_relat_1(sK1) != X13 | ~r2_hidden(X12,k2_relat_1(sK1)) | sK2(X12,X12,X13) = X12 | sK2(X12,X12,X13) = X12 | r2_hidden(sK2(X12,X12,X13),X13)) ) | (spl3_4 | ~spl3_8)),
% 0.20/0.53    inference(superposition,[],[f137,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X0,X1) = X2 | sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f40,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f47,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(rectify,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(flattening,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.53  fof(f137,plain,(
% 0.20/0.53    ( ! [X0] : (k2_relat_1(sK1) != k2_enumset1(X0,X0,X0,X0) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | (spl3_4 | ~spl3_8)),
% 0.20/0.53    inference(superposition,[],[f84,f134])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) != X1 | k2_enumset1(X0,X0,X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f42,f49])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK2(X0,X1,X2) != X1 | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | spl3_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f82])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    spl3_4 <=> k2_relat_1(sK1) = k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.53  fof(f182,plain,(
% 0.20/0.53    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~spl3_17),
% 0.20/0.53    inference(avatar_component_clause,[],[f180])).
% 0.20/0.53  fof(f180,plain,(
% 0.20/0.53    spl3_17 <=> r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.53  fof(f183,plain,(
% 0.20/0.53    ~spl3_5 | ~spl3_1 | ~spl3_2 | spl3_17 | ~spl3_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f176,f103,f180,f72,f67,f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    spl3_5 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    spl3_1 <=> v1_relat_1(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    spl3_2 <=> v1_funct_1(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    spl3_6 <=> k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.53  fof(f176,plain,(
% 0.20/0.53    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~spl3_6),
% 0.20/0.53    inference(superposition,[],[f129,f105])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) | ~spl3_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f103])).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    ( ! [X4,X5] : (r2_hidden(k1_funct_1(X5,X4),k11_relat_1(X5,X4)) | ~v1_funct_1(X5) | ~v1_relat_1(X5) | ~r2_hidden(X4,k1_relat_1(X5))) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f125])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    ( ! [X4,X5] : (~r2_hidden(X4,k1_relat_1(X5)) | ~v1_funct_1(X5) | ~v1_relat_1(X5) | r2_hidden(k1_funct_1(X5,X4),k11_relat_1(X5,X4)) | ~v1_relat_1(X5)) )),
% 0.20/0.53    inference(resolution,[],[f60,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(equality_resolution,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  % (19676)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    ~spl3_1 | ~spl3_2 | spl3_8 | ~spl3_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f120,f114,f133,f72,f67])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    spl3_7 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(k4_tarski(sK0,X0),sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    ( ! [X0] : (k1_funct_1(sK1,sK0) = X0 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl3_7),
% 0.20/0.53    inference(resolution,[],[f34,f115])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(k4_tarski(sK0,X0),sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl3_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f114])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    ~spl3_1 | spl3_7 | ~spl3_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f107,f103,f114,f67])).
% 0.20/0.54  fof(f107,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(k4_tarski(sK0,X0),sK1) | ~v1_relat_1(sK1)) ) | ~spl3_6),
% 0.20/0.54    inference(superposition,[],[f46,f105])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f106,plain,(
% 0.20/0.54    ~spl3_1 | spl3_6 | ~spl3_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f100,f77,f103,f67])).
% 0.20/0.54  % (19681)Refutation not found, incomplete strategy% (19681)------------------------------
% 0.20/0.54  % (19681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    spl3_3 <=> k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.54  % (19681)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (19681)Memory used [KB]: 1663
% 0.20/0.54  % (19681)Time elapsed: 0.142 s
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~spl3_3),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f99])).
% 0.20/0.54  % (19681)------------------------------
% 0.20/0.54  % (19681)------------------------------
% 0.20/0.54  fof(f99,plain,(
% 0.20/0.54    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK1) | ~spl3_3),
% 0.20/0.54    inference(superposition,[],[f36,f97])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    ( ! [X0] : (k11_relat_1(X0,sK0) = k9_relat_1(X0,k1_relat_1(sK1)) | ~v1_relat_1(X0)) ) | ~spl3_3),
% 0.20/0.54    inference(superposition,[],[f59,f79])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f77])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f44,f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f43,f49])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    spl3_5 | ~spl3_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f86,f77,f88])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl3_3),
% 0.20/0.54    inference(superposition,[],[f62,f79])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 0.20/0.54    inference(equality_resolution,[],[f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 0.20/0.54    inference(equality_resolution,[],[f56])).
% 0.20/0.54  % (19661)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.20/0.54    inference(definition_unfolding,[],[f39,f49])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    ~spl3_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f51,f82])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.20/0.54    inference(definition_unfolding,[],[f32,f50])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.54    inference(negated_conjecture,[],[f10])).
% 0.20/0.54  fof(f10,conjecture,(
% 0.20/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    spl3_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f52,f77])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.54    inference(definition_unfolding,[],[f31,f50])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    spl3_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f30,f72])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    v1_funct_1(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    spl3_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f29,f67])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    v1_relat_1(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (19675)------------------------------
% 0.20/0.54  % (19675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19675)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (19675)Memory used [KB]: 10874
% 0.20/0.54  % (19675)Time elapsed: 0.089 s
% 0.20/0.54  % (19675)------------------------------
% 0.20/0.54  % (19675)------------------------------
% 0.20/0.54  % (19664)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (19666)Refutation not found, incomplete strategy% (19666)------------------------------
% 0.20/0.54  % (19666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19666)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (19651)Success in time 0.186 s
% 0.20/0.54  % (19660)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (19673)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
%------------------------------------------------------------------------------

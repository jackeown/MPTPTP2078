%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 250 expanded)
%              Number of leaves         :   17 (  91 expanded)
%              Depth                    :   19
%              Number of atoms          :  358 ( 991 expanded)
%              Number of equality atoms :   51 ( 144 expanded)
%              Maximal formula depth    :   25 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f101,f157,f166,f171,f179,f182,f187,f193,f195])).

fof(f195,plain,
    ( spl7_2
    | spl7_15 ),
    inference(avatar_split_clause,[],[f194,f191,f49])).

fof(f49,plain,
    ( spl7_2
  <=> r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f191,plain,
    ( spl7_15
  <=> r2_hidden(sK4(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f194,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2))
    | spl7_15 ),
    inference(resolution,[],[f192,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f192,plain,
    ( ~ r2_hidden(sK4(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK2))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f191])).

fof(f193,plain,
    ( ~ spl7_15
    | spl7_2 ),
    inference(avatar_split_clause,[],[f189,f49,f191])).

fof(f189,plain,
    ( ~ r2_hidden(sK4(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK2))
    | spl7_2 ),
    inference(resolution,[],[f97,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f97,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f187,plain,
    ( ~ spl7_1
    | spl7_12
    | spl7_12
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f186,f155,f164,f164,f29])).

fof(f29,plain,
    ( spl7_1
  <=> r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f164,plain,
    ( spl7_12
  <=> ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f155,plain,
    ( spl7_11
  <=> ! [X1,X0,X2] :
        ( sK0 != X0
        | ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(X2,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(sK0,X1)
        | ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(sK0,X0) )
    | ~ spl7_11 ),
    inference(equality_resolution,[],[f156])).

fof(f156,plain,
    ( ! [X2,X0,X1] :
        ( sK0 != X0
        | ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(X2,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f155])).

fof(f182,plain,
    ( spl7_13
    | spl7_14 ),
    inference(avatar_split_clause,[],[f180,f177,f169])).

fof(f169,plain,
    ( spl7_13
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f177,plain,
    ( spl7_14
  <=> r2_hidden(sK4(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f180,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | spl7_14 ),
    inference(resolution,[],[f178,f19])).

fof(f178,plain,
    ( ~ r2_hidden(sK4(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | spl7_14 ),
    inference(avatar_component_clause,[],[f177])).

fof(f179,plain,
    ( ~ spl7_14
    | spl7_13 ),
    inference(avatar_split_clause,[],[f175,f169,f177])).

fof(f175,plain,
    ( ~ r2_hidden(sK4(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | spl7_13 ),
    inference(resolution,[],[f170,f20])).

fof(f170,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | spl7_13 ),
    inference(avatar_component_clause,[],[f169])).

fof(f171,plain,
    ( ~ spl7_13
    | ~ spl7_1
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f167,f164,f29,f169])).

fof(f167,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | ~ spl7_1
    | ~ spl7_12 ),
    inference(resolution,[],[f165,f30])).

fof(f30,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f165,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f164])).

fof(f166,plain,
    ( spl7_12
    | ~ spl7_1
    | spl7_12
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f162,f152,f164,f29,f164])).

fof(f152,plain,
    ( spl7_10
  <=> ! [X3,X5,X7,X4,X6] :
        ( ~ r2_hidden(X3,X4)
        | ~ r1_tarski(X4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X6))
        | ~ r2_hidden(X7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X6,X3),sK6(k2_zfmisc_1(sK1,sK2),sK3,X7))
        | ~ r2_hidden(X3,X5)
        | ~ r1_tarski(X5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(sK0,X0)
        | ~ r2_hidden(sK0,X1)
        | ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) )
    | ~ spl7_10 ),
    inference(equality_resolution,[],[f161])).

fof(f161,plain,
    ( ! [X2,X0,X1] :
        ( sK0 != X0
        | ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(X2,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) )
    | ~ spl7_10 ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,
    ( ! [X2,X0,X1] :
        ( sK0 != X0
        | ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(X2,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) )
    | ~ spl7_10 ),
    inference(superposition,[],[f153,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X2
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(trivial_inequality_removal,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( X2 != X2
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X2 ) ),
    inference(duplicate_literal_removal,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( X2 != X2
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X2 ) ),
    inference(equality_factoring,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK5(X1,X2,X0),sK6(X1,X2,X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK5(X1,X2,X3),sK6(X1,X2,X3)) = X3 ) ),
    inference(resolution,[],[f33,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,X0)
      | k4_tarski(sK5(X1,X2,X3),sK6(X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k4_tarski(sK5(X1,X2,X3),sK6(X1,X2,X3)) = X3
        & r2_hidden(sK6(X1,X2,X3),X2)
        & r2_hidden(sK5(X1,X2,X3),X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f10,f15])).

fof(f15,plain,(
    ! [X3,X2,X1] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
     => ( k4_tarski(sK5(X1,X2,X3),sK6(X1,X2,X3)) = X3
        & r2_hidden(sK6(X1,X2,X3),X2)
        & r2_hidden(sK5(X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X2 ) ),
    inference(resolution,[],[f32,f19])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK4(X1,k2_zfmisc_1(X2,X3)),k2_zfmisc_1(X2,X3))
      | k4_tarski(sK5(X2,X3,X0),sK6(X2,X3,X0)) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f25,f20])).

fof(f153,plain,
    ( ! [X6,X4,X7,X5,X3] :
        ( sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X6,X3),sK6(k2_zfmisc_1(sK1,sK2),sK3,X7))
        | ~ r1_tarski(X4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X6))
        | ~ r2_hidden(X7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(X3,X4)
        | ~ r2_hidden(X3,X5)
        | ~ r1_tarski(X5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X6)) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f152])).

fof(f157,plain,
    ( spl7_10
    | spl7_11
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f150,f99,f155,f152])).

fof(f99,plain,
    ( spl7_7
  <=> ! [X1,X3,X0,X2,X4] :
        ( sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X0,X1),X2)
        | ~ r1_tarski(X4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0))
        | ~ r2_hidden(X1,X4)
        | ~ r1_tarski(X3,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X2,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f150,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] :
        ( sK0 != X0
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r1_tarski(X2,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(X3,X4)
        | ~ r1_tarski(X5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X6))
        | ~ r2_hidden(X3,X5)
        | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X6,X3),sK6(k2_zfmisc_1(sK1,sK2),sK3,X7))
        | ~ r2_hidden(X7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r1_tarski(X4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X6)) )
    | ~ spl7_7 ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] :
        ( sK0 != X0
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r1_tarski(X2,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r2_hidden(X3,X4)
        | ~ r1_tarski(X5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X6))
        | ~ r2_hidden(X3,X5)
        | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X6,X3),sK6(k2_zfmisc_1(sK1,sK2),sK3,X7))
        | ~ r2_hidden(X7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
        | ~ r1_tarski(X4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X6))
        | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) )
    | ~ spl7_7 ),
    inference(superposition,[],[f117,f38])).

fof(f117,plain,
    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
        ( sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X2,X0),sK6(X3,sK3,X4))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X4,k2_zfmisc_1(X3,sK3))
        | ~ r1_tarski(X5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X2))
        | ~ r2_hidden(X0,X5)
        | ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X2))
        | ~ r2_hidden(X6,X7)
        | ~ r1_tarski(X8,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X9))
        | ~ r2_hidden(X6,X8)
        | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X9,X6),sK6(X3,sK3,X10))
        | ~ r2_hidden(X10,k2_zfmisc_1(X3,sK3))
        | ~ r1_tarski(X7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X9)) )
    | ~ spl7_7 ),
    inference(resolution,[],[f116,f112])).

fof(f112,plain,
    ( ! [X14,X12,X17,X15,X13,X18,X16] :
        ( ~ r1_tarski(X18,k2_zfmisc_1(X16,sK3))
        | ~ r2_hidden(X14,X12)
        | ~ r1_tarski(X15,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X13))
        | ~ r2_hidden(X14,X15)
        | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X13,X14),sK6(X16,sK3,X17))
        | ~ r2_hidden(X17,X18)
        | ~ r1_tarski(X12,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X13)) )
    | ~ spl7_7 ),
    inference(resolution,[],[f100,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK6(X1,X2,X3),X2)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f100,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r2_hidden(X2,sK3)
        | ~ r1_tarski(X4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0))
        | ~ r2_hidden(X1,X4)
        | ~ r1_tarski(X3,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0))
        | ~ r2_hidden(X1,X3)
        | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X0,X1),X2) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f116,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( r1_tarski(k2_zfmisc_1(X3,sK3),k2_zfmisc_1(X3,sK3))
        | ~ r2_hidden(X2,X0)
        | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X1,X2),sK6(X3,sK3,X4))
        | ~ r2_hidden(X4,k2_zfmisc_1(X3,sK3))
        | ~ r1_tarski(X5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X1))
        | ~ r2_hidden(X2,X5)
        | ~ r1_tarski(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X1)) )
    | ~ spl7_7 ),
    inference(resolution,[],[f113,f19])).

fof(f113,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( ~ r2_hidden(sK4(X6,k2_zfmisc_1(X4,sK3)),k2_zfmisc_1(X4,sK3))
        | ~ r1_tarski(X2,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X3))
        | ~ r2_hidden(X0,X2)
        | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X3,X0),sK6(X4,sK3,X5))
        | ~ r2_hidden(X5,X6)
        | ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X3))
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_7 ),
    inference(resolution,[],[f112,f20])).

fof(f101,plain,
    ( ~ spl7_2
    | spl7_7
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f96,f49,f99,f49])).

fof(f96,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X0,X1),X2)
        | ~ r2_hidden(X2,sK3)
        | ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2))
        | ~ r2_hidden(X1,X3)
        | ~ r1_tarski(X3,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0))
        | ~ r2_hidden(X1,X4)
        | ~ r1_tarski(X4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f94,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X1,X2,X3),X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f94,plain,
    ( ! [X6,X4,X7,X5,X3] :
        ( ~ r2_hidden(sK5(k2_zfmisc_1(sK1,sK2),X4,X5),X6)
        | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X4,X5),X3)
        | ~ r2_hidden(X3,sK3)
        | ~ r1_tarski(X6,k2_zfmisc_1(sK1,sK2))
        | ~ r2_hidden(X5,X7)
        | ~ r1_tarski(X7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X4)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f67,f23])).

fof(f67,plain,
    ( ! [X4,X2,X3] :
        ( ~ r2_hidden(X3,k2_zfmisc_1(sK1,sK2))
        | ~ r2_hidden(X2,sK3)
        | sK0 != k4_tarski(X3,X2)
        | ~ r2_hidden(X3,X4)
        | ~ r1_tarski(X4,k2_zfmisc_1(sK1,sK2)) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,
    ( ! [X4,X2,X3] :
        ( ~ r2_hidden(X2,sK3)
        | ~ r2_hidden(X3,k2_zfmisc_1(sK1,sK2))
        | ~ r2_hidden(X3,k2_zfmisc_1(sK1,sK2))
        | sK0 != k4_tarski(X3,X2)
        | ~ r2_hidden(X3,X4)
        | ~ r1_tarski(X4,k2_zfmisc_1(sK1,sK2)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f50,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X0,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X0,X2)
      | k4_tarski(X0,X1) != sK0
      | ~ r2_hidden(X0,X3)
      | ~ r1_tarski(X3,k2_zfmisc_1(sK1,sK2)) ) ),
    inference(resolution,[],[f41,f23])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(X2,sK2,X1),sK1)
      | sK0 != k4_tarski(X1,X0)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,k2_zfmisc_1(X2,sK2))
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,k2_zfmisc_1(X2,sK2)) ) ),
    inference(resolution,[],[f40,f24])).

fof(f40,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_hidden(sK6(X3,X4,X5),sK2)
      | ~ r2_hidden(X6,sK3)
      | sK0 != k4_tarski(X5,X6)
      | ~ r2_hidden(sK5(X3,X4,X5),sK1)
      | ~ r2_hidden(X5,k2_zfmisc_1(X3,X4)) ) ),
    inference(superposition,[],[f26,f38])).

fof(f26,plain,(
    ! [X6,X4,X5] :
      ( sK0 != k4_tarski(k4_tarski(X4,X5),X6)
      | ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f18,plain,(
    ! [X6,X4,X5] :
      ( k3_mcart_1(X4,X5,X6) != sK0
      | ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ! [X4,X5,X6] :
        ( k3_mcart_1(X4,X5,X6) != sK0
        | ~ r2_hidden(X6,sK3)
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X4,sK1) )
    & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5,X6] :
            ( k3_mcart_1(X4,X5,X6) != X0
            | ~ r2_hidden(X6,X3)
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) )
   => ( ! [X6,X5,X4] :
          ( k3_mcart_1(X4,X5,X6) != sK0
          | ~ r2_hidden(X6,sK3)
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK1) )
      & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) != X0
          | ~ r2_hidden(X6,X3)
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5,X6] :
              ~ ( k3_mcart_1(X4,X5,X6) = X0
                & r2_hidden(X6,X3)
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5,X6] :
            ~ ( k3_mcart_1(X4,X5,X6) = X0
              & r2_hidden(X6,X3)
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_mcart_1)).

fof(f50,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f31,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f27,f29])).

fof(f27,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f17,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f17,plain,(
    r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n010.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 20:40:14 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.50  % (27261)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (27278)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (27251)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (27247)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (27251)Refutation not found, incomplete strategy% (27251)------------------------------
% 0.21/0.51  % (27251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27251)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (27251)Memory used [KB]: 6140
% 0.21/0.51  % (27251)Time elapsed: 0.107 s
% 0.21/0.51  % (27251)------------------------------
% 0.21/0.51  % (27251)------------------------------
% 0.21/0.52  % (27255)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (27271)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (27267)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (27258)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (27282)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (27257)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (27275)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (27262)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (27248)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (27285)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (27282)Refutation not found, incomplete strategy% (27282)------------------------------
% 0.21/0.54  % (27282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27271)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (27257)Refutation not found, incomplete strategy% (27257)------------------------------
% 0.21/0.54  % (27257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27257)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27257)Memory used [KB]: 10618
% 0.21/0.54  % (27257)Time elapsed: 0.112 s
% 0.21/0.54  % (27257)------------------------------
% 0.21/0.54  % (27257)------------------------------
% 0.21/0.54  % (27249)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (27282)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27282)Memory used [KB]: 10618
% 0.21/0.54  % (27282)Time elapsed: 0.112 s
% 0.21/0.54  % (27282)------------------------------
% 0.21/0.54  % (27282)------------------------------
% 0.21/0.54  % (27249)Refutation not found, incomplete strategy% (27249)------------------------------
% 0.21/0.54  % (27249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27249)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27249)Memory used [KB]: 10618
% 0.21/0.54  % (27249)Time elapsed: 0.137 s
% 0.21/0.54  % (27249)------------------------------
% 0.21/0.54  % (27249)------------------------------
% 0.21/0.54  % (27255)Refutation not found, incomplete strategy% (27255)------------------------------
% 0.21/0.54  % (27255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27255)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27255)Memory used [KB]: 10618
% 0.21/0.54  % (27255)Time elapsed: 0.136 s
% 0.21/0.54  % (27255)------------------------------
% 0.21/0.54  % (27255)------------------------------
% 0.21/0.54  % (27284)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (27252)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (27256)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (27253)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (27280)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (27263)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (27273)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (27279)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (27281)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f196,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f31,f101,f157,f166,f171,f179,f182,f187,f193,f195])).
% 0.21/0.55  fof(f195,plain,(
% 0.21/0.55    spl7_2 | spl7_15),
% 0.21/0.55    inference(avatar_split_clause,[],[f194,f191,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    spl7_2 <=> r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.55  fof(f191,plain,(
% 0.21/0.55    spl7_15 <=> r2_hidden(sK4(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.55  fof(f194,plain,(
% 0.21/0.55    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2)) | spl7_15),
% 0.21/0.55    inference(resolution,[],[f192,f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,plain,(
% 0.21/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.21/0.55    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f192,plain,(
% 0.21/0.55    ~r2_hidden(sK4(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK2)) | spl7_15),
% 0.21/0.55    inference(avatar_component_clause,[],[f191])).
% 0.21/0.55  fof(f193,plain,(
% 0.21/0.55    ~spl7_15 | spl7_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f189,f49,f191])).
% 0.21/0.55  fof(f189,plain,(
% 0.21/0.55    ~r2_hidden(sK4(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK2)) | spl7_2),
% 0.21/0.55    inference(resolution,[],[f97,f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    ~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2)) | spl7_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f49])).
% 0.21/0.55  fof(f187,plain,(
% 0.21/0.55    ~spl7_1 | spl7_12 | spl7_12 | ~spl7_11),
% 0.21/0.55    inference(avatar_split_clause,[],[f186,f155,f164,f164,f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    spl7_1 <=> r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.55  fof(f164,plain,(
% 0.21/0.55    spl7_12 <=> ! [X1] : (~r2_hidden(sK0,X1) | ~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.55  fof(f155,plain,(
% 0.21/0.55    spl7_11 <=> ! [X1,X0,X2] : (sK0 != X0 | ~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,X2) | ~r1_tarski(X2,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,X1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.55  fof(f186,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(sK0,X1) | ~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(sK0,X0)) ) | ~spl7_11),
% 0.21/0.55    inference(equality_resolution,[],[f156])).
% 0.21/0.55  fof(f156,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (sK0 != X0 | ~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,X2) | ~r1_tarski(X2,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,X1)) ) | ~spl7_11),
% 0.21/0.55    inference(avatar_component_clause,[],[f155])).
% 0.21/0.55  fof(f182,plain,(
% 0.21/0.55    spl7_13 | spl7_14),
% 0.21/0.55    inference(avatar_split_clause,[],[f180,f177,f169])).
% 0.21/0.55  fof(f169,plain,(
% 0.21/0.55    spl7_13 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.55  fof(f177,plain,(
% 0.21/0.55    spl7_14 <=> r2_hidden(sK4(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.55  fof(f180,plain,(
% 0.21/0.55    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | spl7_14),
% 0.21/0.55    inference(resolution,[],[f178,f19])).
% 0.21/0.55  fof(f178,plain,(
% 0.21/0.55    ~r2_hidden(sK4(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | spl7_14),
% 0.21/0.55    inference(avatar_component_clause,[],[f177])).
% 0.21/0.55  fof(f179,plain,(
% 0.21/0.55    ~spl7_14 | spl7_13),
% 0.21/0.55    inference(avatar_split_clause,[],[f175,f169,f177])).
% 0.21/0.55  fof(f175,plain,(
% 0.21/0.55    ~r2_hidden(sK4(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | spl7_13),
% 0.21/0.55    inference(resolution,[],[f170,f20])).
% 0.21/0.55  fof(f170,plain,(
% 0.21/0.55    ~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | spl7_13),
% 0.21/0.55    inference(avatar_component_clause,[],[f169])).
% 0.21/0.55  fof(f171,plain,(
% 0.21/0.55    ~spl7_13 | ~spl7_1 | ~spl7_12),
% 0.21/0.55    inference(avatar_split_clause,[],[f167,f164,f29,f169])).
% 0.21/0.55  fof(f167,plain,(
% 0.21/0.55    ~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | (~spl7_1 | ~spl7_12)),
% 0.21/0.55    inference(resolution,[],[f165,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~spl7_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f29])).
% 0.21/0.55  fof(f165,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(sK0,X1) | ~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))) ) | ~spl7_12),
% 0.21/0.55    inference(avatar_component_clause,[],[f164])).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    spl7_12 | ~spl7_1 | spl7_12 | ~spl7_10),
% 0.21/0.55    inference(avatar_split_clause,[],[f162,f152,f164,f29,f164])).
% 0.21/0.55  fof(f152,plain,(
% 0.21/0.55    spl7_10 <=> ! [X3,X5,X7,X4,X6] : (~r2_hidden(X3,X4) | ~r1_tarski(X4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X6)) | ~r2_hidden(X7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X6,X3),sK6(k2_zfmisc_1(sK1,sK2),sK3,X7)) | ~r2_hidden(X3,X5) | ~r1_tarski(X5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X6)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.55  fof(f162,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(sK0,X0) | ~r2_hidden(sK0,X1) | ~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))) ) | ~spl7_10),
% 0.21/0.55    inference(equality_resolution,[],[f161])).
% 0.21/0.55  fof(f161,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (sK0 != X0 | ~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2) | ~r1_tarski(X2,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))) ) | ~spl7_10),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f158])).
% 0.21/0.55  fof(f158,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (sK0 != X0 | ~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2) | ~r1_tarski(X2,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))) ) | ~spl7_10),
% 0.21/0.55    inference(superposition,[],[f153,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X2 | ~r2_hidden(X2,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (X2 != X2 | ~r2_hidden(X2,k2_zfmisc_1(X0,X1)) | k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X2) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (X2 != X2 | ~r2_hidden(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X2,k2_zfmisc_1(X0,X1)) | k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X2) )),
% 0.21/0.55    inference(equality_factoring,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_tarski(sK5(X1,X2,X0),sK6(X1,X2,X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ~r2_hidden(X3,k2_zfmisc_1(X1,X2)) | k4_tarski(sK5(X1,X2,X3),sK6(X1,X2,X3)) = X3) )),
% 0.21/0.55    inference(resolution,[],[f33,f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~r2_hidden(X3,X0) | k4_tarski(sK5(X1,X2,X3),sK6(X1,X2,X3)) = X3) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((k4_tarski(sK5(X1,X2,X3),sK6(X1,X2,X3)) = X3 & r2_hidden(sK6(X1,X2,X3),X2) & r2_hidden(sK5(X1,X2,X3),X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f10,f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X3,X2,X1] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) => (k4_tarski(sK5(X1,X2,X3),sK6(X1,X2,X3)) = X3 & r2_hidden(sK6(X1,X2,X3),X2) & r2_hidden(sK5(X1,X2,X3),X1)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X2,k2_zfmisc_1(X0,X1)) | k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X2) )),
% 0.21/0.55    inference(resolution,[],[f32,f19])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK4(X1,k2_zfmisc_1(X2,X3)),k2_zfmisc_1(X2,X3)) | k4_tarski(sK5(X2,X3,X0),sK6(X2,X3,X0)) = X0 | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(resolution,[],[f25,f20])).
% 0.21/0.55  fof(f153,plain,(
% 0.21/0.55    ( ! [X6,X4,X7,X5,X3] : (sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X6,X3),sK6(k2_zfmisc_1(sK1,sK2),sK3,X7)) | ~r1_tarski(X4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X6)) | ~r2_hidden(X7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X3,X4) | ~r2_hidden(X3,X5) | ~r1_tarski(X5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X6))) ) | ~spl7_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f152])).
% 0.21/0.55  fof(f157,plain,(
% 0.21/0.55    spl7_10 | spl7_11 | ~spl7_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f150,f99,f155,f152])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    spl7_7 <=> ! [X1,X3,X0,X2,X4] : (sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X0,X1),X2) | ~r1_tarski(X4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0)) | ~r2_hidden(X1,X4) | ~r1_tarski(X3,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0)) | ~r2_hidden(X1,X3) | ~r2_hidden(X2,sK3))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.55  fof(f150,plain,(
% 0.21/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sK0 != X0 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r1_tarski(X2,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,X2) | ~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X3,X4) | ~r1_tarski(X5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X6)) | ~r2_hidden(X3,X5) | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X6,X3),sK6(k2_zfmisc_1(sK1,sK2),sK3,X7)) | ~r2_hidden(X7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r1_tarski(X4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X6))) ) | ~spl7_7),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f147])).
% 0.21/0.55  fof(f147,plain,(
% 0.21/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sK0 != X0 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r1_tarski(X2,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X0,X2) | ~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X3,X4) | ~r1_tarski(X5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X6)) | ~r2_hidden(X3,X5) | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X6,X3),sK6(k2_zfmisc_1(sK1,sK2),sK3,X7)) | ~r2_hidden(X7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r1_tarski(X4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X6)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))) ) | ~spl7_7),
% 0.21/0.55    inference(superposition,[],[f117,f38])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X2,X0),sK6(X3,sK3,X4)) | ~r2_hidden(X0,X1) | ~r2_hidden(X4,k2_zfmisc_1(X3,sK3)) | ~r1_tarski(X5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X2)) | ~r2_hidden(X0,X5) | ~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X2)) | ~r2_hidden(X6,X7) | ~r1_tarski(X8,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X9)) | ~r2_hidden(X6,X8) | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X9,X6),sK6(X3,sK3,X10)) | ~r2_hidden(X10,k2_zfmisc_1(X3,sK3)) | ~r1_tarski(X7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X9))) ) | ~spl7_7),
% 0.21/0.55    inference(resolution,[],[f116,f112])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    ( ! [X14,X12,X17,X15,X13,X18,X16] : (~r1_tarski(X18,k2_zfmisc_1(X16,sK3)) | ~r2_hidden(X14,X12) | ~r1_tarski(X15,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X13)) | ~r2_hidden(X14,X15) | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X13,X14),sK6(X16,sK3,X17)) | ~r2_hidden(X17,X18) | ~r1_tarski(X12,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X13))) ) | ~spl7_7),
% 0.21/0.55    inference(resolution,[],[f100,f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(sK6(X1,X2,X3),X2) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X2,sK3) | ~r1_tarski(X4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0)) | ~r2_hidden(X1,X4) | ~r1_tarski(X3,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0)) | ~r2_hidden(X1,X3) | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X0,X1),X2)) ) | ~spl7_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f99])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tarski(k2_zfmisc_1(X3,sK3),k2_zfmisc_1(X3,sK3)) | ~r2_hidden(X2,X0) | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X1,X2),sK6(X3,sK3,X4)) | ~r2_hidden(X4,k2_zfmisc_1(X3,sK3)) | ~r1_tarski(X5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X1)) | ~r2_hidden(X2,X5) | ~r1_tarski(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X1))) ) | ~spl7_7),
% 0.21/0.55    inference(resolution,[],[f113,f19])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~r2_hidden(sK4(X6,k2_zfmisc_1(X4,sK3)),k2_zfmisc_1(X4,sK3)) | ~r1_tarski(X2,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X3)) | ~r2_hidden(X0,X2) | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X3,X0),sK6(X4,sK3,X5)) | ~r2_hidden(X5,X6) | ~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X3)) | ~r2_hidden(X0,X1)) ) | ~spl7_7),
% 0.21/0.55    inference(resolution,[],[f112,f20])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ~spl7_2 | spl7_7 | ~spl7_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f96,f49,f99,f49])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X0,X1),X2) | ~r2_hidden(X2,sK3) | ~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0)) | ~r2_hidden(X1,X4) | ~r1_tarski(X4,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0))) ) | ~spl7_2),
% 0.21/0.55    inference(resolution,[],[f94,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(sK5(X1,X2,X3),X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    ( ! [X6,X4,X7,X5,X3] : (~r2_hidden(sK5(k2_zfmisc_1(sK1,sK2),X4,X5),X6) | sK0 != k4_tarski(sK5(k2_zfmisc_1(sK1,sK2),X4,X5),X3) | ~r2_hidden(X3,sK3) | ~r1_tarski(X6,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X5,X7) | ~r1_tarski(X7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X4))) ) | ~spl7_2),
% 0.21/0.55    inference(resolution,[],[f67,f23])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X4,X2,X3] : (~r2_hidden(X3,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X2,sK3) | sK0 != k4_tarski(X3,X2) | ~r2_hidden(X3,X4) | ~r1_tarski(X4,k2_zfmisc_1(sK1,sK2))) ) | ~spl7_2),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X4,X2,X3] : (~r2_hidden(X2,sK3) | ~r2_hidden(X3,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X3,k2_zfmisc_1(sK1,sK2)) | sK0 != k4_tarski(X3,X2) | ~r2_hidden(X3,X4) | ~r1_tarski(X4,k2_zfmisc_1(sK1,sK2))) ) | ~spl7_2),
% 0.21/0.55    inference(resolution,[],[f50,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X1,sK3) | ~r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X0,X2) | k4_tarski(X0,X1) != sK0 | ~r2_hidden(X0,X3) | ~r1_tarski(X3,k2_zfmisc_1(sK1,sK2))) )),
% 0.21/0.55    inference(resolution,[],[f41,f23])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK5(X2,sK2,X1),sK1) | sK0 != k4_tarski(X1,X0) | ~r2_hidden(X0,sK3) | ~r2_hidden(X1,k2_zfmisc_1(X2,sK2)) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,k2_zfmisc_1(X2,sK2))) )),
% 0.21/0.55    inference(resolution,[],[f40,f24])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X6,X4,X5,X3] : (~r2_hidden(sK6(X3,X4,X5),sK2) | ~r2_hidden(X6,sK3) | sK0 != k4_tarski(X5,X6) | ~r2_hidden(sK5(X3,X4,X5),sK1) | ~r2_hidden(X5,k2_zfmisc_1(X3,X4))) )),
% 0.21/0.55    inference(superposition,[],[f26,f38])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ( ! [X6,X4,X5] : (sK0 != k4_tarski(k4_tarski(X4,X5),X6) | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f18,f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ( ! [X6,X4,X5] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3] : (! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != X0 | ~r2_hidden(X6,X3) | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))) => (! [X6,X5,X4] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f8,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3] : (! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != X0 | ~r2_hidden(X6,X3) | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2,X3] : ~(! [X4,X5,X6] : ~(k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.21/0.55    inference(negated_conjecture,[],[f5])).
% 0.21/0.55  fof(f5,conjecture,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ~(! [X4,X5,X6] : ~(k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_mcart_1)).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2)) | ~spl7_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f49])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    spl7_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f27,f29])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.21/0.55    inference(definition_unfolding,[],[f17,f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3))),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (27271)------------------------------
% 0.21/0.55  % (27271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27271)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (27271)Memory used [KB]: 10874
% 0.21/0.55  % (27271)Time elapsed: 0.134 s
% 0.21/0.55  % (27271)------------------------------
% 0.21/0.55  % (27271)------------------------------
% 0.21/0.55  % (27245)Success in time 0.191 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 296 expanded)
%              Number of leaves         :   12 (  81 expanded)
%              Depth                    :   21
%              Number of atoms          :  256 (1102 expanded)
%              Number of equality atoms :   90 ( 432 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f292,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f112,f200,f242,f291])).

fof(f291,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f289])).

fof(f289,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_7 ),
    inference(superposition,[],[f256,f173])).

fof(f173,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl4_7
  <=> ! [X0] : k1_xboole_0 = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f256,plain,
    ( k1_xboole_0 != sK1
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f22,f173])).

fof(f22,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f242,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f240])).

fof(f240,plain,
    ( sK0 != sK0
    | ~ spl4_1 ),
    inference(superposition,[],[f22,f235])).

fof(f235,plain,
    ( sK0 = sK1
    | ~ spl4_1 ),
    inference(resolution,[],[f44,f228])).

fof(f228,plain,
    ( r2_hidden(sK1,k2_tarski(sK0,sK0))
    | ~ spl4_1 ),
    inference(superposition,[],[f43,f57])).

fof(f57,plain,
    ( k2_tarski(sK0,sK0) = k2_tarski(sK1,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl4_1
  <=> k2_tarski(sK0,sK0) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f43,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f28,f23])).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f44,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f27,f23])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f200,plain,
    ( spl4_7
    | ~ spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f199,f59,f103,f172])).

fof(f103,plain,
    ( spl4_3
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f59,plain,
    ( spl4_2
  <=> k1_xboole_0 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl4_2 ),
    inference(condensation,[],[f198])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK0,k1_xboole_0)
        | ~ r2_hidden(sK0,X0)
        | k1_xboole_0 = X1 )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f197,f129])).

fof(f129,plain,
    ( ! [X3] : sK0 = X3
    | ~ spl4_2 ),
    inference(resolution,[],[f125,f69])).

fof(f69,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl4_2 ),
    inference(superposition,[],[f43,f61])).

fof(f61,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f125,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | X2 = X3 ) ),
    inference(resolution,[],[f49,f46])).

fof(f46,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f32,f23])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k2_tarski(X2,X2))
      | ~ r2_hidden(X0,X1)
      | X0 = X2 ) ),
    inference(resolution,[],[f24,f44])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(X0,k1_xboole_0),k1_xboole_0)
        | ~ r2_hidden(sK0,X0)
        | k1_xboole_0 = X1 )
    | ~ spl4_2 ),
    inference(condensation,[],[f196])).

fof(f196,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK0,X0)
        | k1_xboole_0 = X1
        | ~ r2_hidden(sK2(X0,k1_xboole_0),X2)
        | ~ r2_hidden(sK2(X0,k1_xboole_0),k1_xboole_0) )
    | ~ spl4_2 ),
    inference(condensation,[],[f195])).

fof(f195,plain,
    ( ! [X6,X4,X5,X3] :
        ( ~ r2_hidden(sK0,X6)
        | ~ r2_hidden(sK0,X4)
        | k1_xboole_0 = X3
        | ~ r2_hidden(sK2(X4,k1_xboole_0),X5)
        | ~ r2_hidden(sK2(X6,k1_xboole_0),k1_xboole_0) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f159,f129])).

fof(f159,plain,
    ( ! [X6,X4,X5,X3] :
        ( ~ r2_hidden(sK0,X4)
        | k1_xboole_0 = X3
        | ~ r2_hidden(sK2(X5,k1_xboole_0),X6)
        | ~ r2_hidden(sK2(X4,k1_xboole_0),X5)
        | ~ r2_hidden(sK2(X6,k1_xboole_0),k1_xboole_0) )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f123,f129])).

fof(f123,plain,
    ( ! [X6,X4,X5,X3] :
        ( k1_xboole_0 = X3
        | ~ r2_hidden(sK2(X3,k1_xboole_0),X4)
        | ~ r2_hidden(sK2(X5,k1_xboole_0),X6)
        | ~ r2_hidden(sK2(X4,k1_xboole_0),X5)
        | ~ r2_hidden(sK2(X6,k1_xboole_0),k1_xboole_0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f118,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f118,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ r1_tarski(X5,k1_xboole_0)
        | k1_xboole_0 = X4
        | ~ r2_hidden(sK2(X4,k1_xboole_0),X2)
        | ~ r2_hidden(sK2(X3,k1_xboole_0),X5)
        | ~ r2_hidden(sK2(X2,k1_xboole_0),X3) )
    | ~ spl4_2 ),
    inference(resolution,[],[f94,f24])).

fof(f94,plain,
    ( ! [X4,X2,X3] :
        ( ~ r2_hidden(sK2(X4,k1_xboole_0),k1_xboole_0)
        | ~ r2_hidden(sK2(X3,k1_xboole_0),X4)
        | k1_xboole_0 = X2
        | ~ r2_hidden(sK2(X2,k1_xboole_0),X3) )
    | ~ spl4_2 ),
    inference(resolution,[],[f89,f26])).

fof(f89,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_tarski(X3,k1_xboole_0)
        | ~ r2_hidden(sK2(X1,k1_xboole_0),X2)
        | ~ r2_hidden(sK2(X2,k1_xboole_0),X3)
        | k1_xboole_0 = X1 )
    | ~ spl4_2 ),
    inference(resolution,[],[f84,f24])).

fof(f84,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(sK2(X2,k1_xboole_0),k1_xboole_0)
        | k1_xboole_0 = X1
        | ~ r2_hidden(sK2(X1,k1_xboole_0),X2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f79,f26])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | ~ r2_hidden(sK2(X0,k1_xboole_0),X1)
        | k1_xboole_0 = X0 )
    | ~ spl4_2 ),
    inference(resolution,[],[f75,f24])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(X0,k1_xboole_0),k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl4_2 ),
    inference(resolution,[],[f70,f26])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X0 )
    | ~ spl4_2 ),
    inference(superposition,[],[f41,f61])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X1))
      | k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f31,f23,f23])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f112,plain,
    ( ~ spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl4_2
    | spl4_3 ),
    inference(resolution,[],[f105,f69])).

fof(f105,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f62,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f50,f59,f55])).

fof(f50,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | k2_tarski(sK0,sK0) = k2_tarski(sK1,sK1) ),
    inference(resolution,[],[f41,f34])).

fof(f34,plain,(
    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) ),
    inference(definition_unfolding,[],[f21,f23,f23])).

fof(f21,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (5057)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (5045)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (5052)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (5057)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (5045)Refutation not found, incomplete strategy% (5045)------------------------------
% 0.20/0.51  % (5045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5045)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5045)Memory used [KB]: 1663
% 0.20/0.51  % (5045)Time elapsed: 0.094 s
% 0.20/0.51  % (5045)------------------------------
% 0.20/0.51  % (5045)------------------------------
% 0.20/0.51  % (5060)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (5073)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (5049)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (5067)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (5050)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (5047)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (5065)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (5053)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f292,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f62,f112,f200,f242,f291])).
% 0.20/0.52  fof(f291,plain,(
% 0.20/0.52    ~spl4_7),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f290])).
% 0.20/0.52  fof(f290,plain,(
% 0.20/0.52    $false | ~spl4_7),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f289])).
% 0.20/0.52  fof(f289,plain,(
% 0.20/0.52    k1_xboole_0 != k1_xboole_0 | ~spl4_7),
% 0.20/0.52    inference(superposition,[],[f256,f173])).
% 0.20/0.52  fof(f173,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl4_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f172])).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    spl4_7 <=> ! [X0] : k1_xboole_0 = X0),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.52  fof(f256,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | ~spl4_7),
% 0.20/0.52    inference(backward_demodulation,[],[f22,f173])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    sK0 != sK1),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f7,plain,(
% 0.20/0.52    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.52    inference(negated_conjecture,[],[f5])).
% 0.20/0.52  fof(f5,conjecture,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 0.20/0.52  fof(f242,plain,(
% 0.20/0.52    ~spl4_1),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f241])).
% 0.20/0.52  fof(f241,plain,(
% 0.20/0.52    $false | ~spl4_1),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f240])).
% 0.20/0.52  fof(f240,plain,(
% 0.20/0.52    sK0 != sK0 | ~spl4_1),
% 0.20/0.52    inference(superposition,[],[f22,f235])).
% 0.20/0.52  fof(f235,plain,(
% 0.20/0.52    sK0 = sK1 | ~spl4_1),
% 0.20/0.52    inference(resolution,[],[f44,f228])).
% 0.20/0.52  fof(f228,plain,(
% 0.20/0.52    r2_hidden(sK1,k2_tarski(sK0,sK0)) | ~spl4_1),
% 0.20/0.52    inference(superposition,[],[f43,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    k2_tarski(sK0,sK0) = k2_tarski(sK1,sK1) | ~spl4_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    spl4_1 <=> k2_tarski(sK0,sK0) = k2_tarski(sK1,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 0.20/0.52    inference(equality_resolution,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 0.20/0.52    inference(equality_resolution,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 0.20/0.52    inference(definition_unfolding,[],[f28,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.52    inference(rectify,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 0.20/0.52    inference(equality_resolution,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 0.20/0.52    inference(definition_unfolding,[],[f27,f23])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f200,plain,(
% 0.20/0.52    spl4_7 | ~spl4_3 | ~spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f199,f59,f103,f172])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    spl4_3 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    spl4_2 <=> k1_xboole_0 = k2_tarski(sK0,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.52  fof(f199,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl4_2),
% 0.20/0.52    inference(condensation,[],[f198])).
% 0.20/0.52  fof(f198,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK0,k1_xboole_0) | ~r2_hidden(sK0,X0) | k1_xboole_0 = X1) ) | ~spl4_2),
% 0.20/0.52    inference(forward_demodulation,[],[f197,f129])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    ( ! [X3] : (sK0 = X3) ) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f125,f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    r2_hidden(sK0,k1_xboole_0) | ~spl4_2),
% 0.20/0.52    inference(superposition,[],[f43,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    k1_xboole_0 = k2_tarski(sK0,sK0) | ~spl4_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f59])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r2_hidden(X2,k1_xboole_0) | X2 = X3) )),
% 0.20/0.52    inference(resolution,[],[f49,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_tarski(X1,X1)) | k1_xboole_0 != X0) )),
% 0.20/0.52    inference(definition_unfolding,[],[f32,f23])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X1,k2_tarski(X2,X2)) | ~r2_hidden(X0,X1) | X0 = X2) )),
% 0.20/0.52    inference(resolution,[],[f24,f44])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(rectify,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f197,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,k1_xboole_0),k1_xboole_0) | ~r2_hidden(sK0,X0) | k1_xboole_0 = X1) ) | ~spl4_2),
% 0.20/0.52    inference(condensation,[],[f196])).
% 0.20/0.52  fof(f196,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK0,X0) | k1_xboole_0 = X1 | ~r2_hidden(sK2(X0,k1_xboole_0),X2) | ~r2_hidden(sK2(X0,k1_xboole_0),k1_xboole_0)) ) | ~spl4_2),
% 0.20/0.52    inference(condensation,[],[f195])).
% 0.20/0.52  fof(f195,plain,(
% 0.20/0.52    ( ! [X6,X4,X5,X3] : (~r2_hidden(sK0,X6) | ~r2_hidden(sK0,X4) | k1_xboole_0 = X3 | ~r2_hidden(sK2(X4,k1_xboole_0),X5) | ~r2_hidden(sK2(X6,k1_xboole_0),k1_xboole_0)) ) | ~spl4_2),
% 0.20/0.52    inference(forward_demodulation,[],[f159,f129])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    ( ! [X6,X4,X5,X3] : (~r2_hidden(sK0,X4) | k1_xboole_0 = X3 | ~r2_hidden(sK2(X5,k1_xboole_0),X6) | ~r2_hidden(sK2(X4,k1_xboole_0),X5) | ~r2_hidden(sK2(X6,k1_xboole_0),k1_xboole_0)) ) | ~spl4_2),
% 0.20/0.52    inference(backward_demodulation,[],[f123,f129])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    ( ! [X6,X4,X5,X3] : (k1_xboole_0 = X3 | ~r2_hidden(sK2(X3,k1_xboole_0),X4) | ~r2_hidden(sK2(X5,k1_xboole_0),X6) | ~r2_hidden(sK2(X4,k1_xboole_0),X5) | ~r2_hidden(sK2(X6,k1_xboole_0),k1_xboole_0)) ) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f118,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    ( ! [X4,X2,X5,X3] : (~r1_tarski(X5,k1_xboole_0) | k1_xboole_0 = X4 | ~r2_hidden(sK2(X4,k1_xboole_0),X2) | ~r2_hidden(sK2(X3,k1_xboole_0),X5) | ~r2_hidden(sK2(X2,k1_xboole_0),X3)) ) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f94,f24])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    ( ! [X4,X2,X3] : (~r2_hidden(sK2(X4,k1_xboole_0),k1_xboole_0) | ~r2_hidden(sK2(X3,k1_xboole_0),X4) | k1_xboole_0 = X2 | ~r2_hidden(sK2(X2,k1_xboole_0),X3)) ) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f89,f26])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    ( ! [X2,X3,X1] : (~r1_tarski(X3,k1_xboole_0) | ~r2_hidden(sK2(X1,k1_xboole_0),X2) | ~r2_hidden(sK2(X2,k1_xboole_0),X3) | k1_xboole_0 = X1) ) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f84,f24])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~r2_hidden(sK2(X2,k1_xboole_0),k1_xboole_0) | k1_xboole_0 = X1 | ~r2_hidden(sK2(X1,k1_xboole_0),X2)) ) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f79,f26])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | ~r2_hidden(sK2(X0,k1_xboole_0),X1) | k1_xboole_0 = X0) ) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f75,f24])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK2(X0,k1_xboole_0),k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f70,f26])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl4_2),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X0) ) | ~spl4_2),
% 0.20/0.52    inference(superposition,[],[f41,f61])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X1)) | k1_xboole_0 = X0 | k2_tarski(X1,X1) = X0) )),
% 0.20/0.52    inference(definition_unfolding,[],[f31,f23,f23])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    ~spl4_2 | spl4_3),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f110])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    $false | (~spl4_2 | spl4_3)),
% 0.20/0.52    inference(resolution,[],[f105,f69])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k1_xboole_0) | spl4_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f103])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    spl4_1 | spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f50,f59,f55])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    k1_xboole_0 = k2_tarski(sK0,sK0) | k2_tarski(sK0,sK0) = k2_tarski(sK1,sK1)),
% 0.20/0.52    inference(resolution,[],[f41,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))),
% 0.20/0.52    inference(definition_unfolding,[],[f21,f23,f23])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (5057)------------------------------
% 0.20/0.52  % (5057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5057)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (5057)Memory used [KB]: 6268
% 0.20/0.52  % (5057)Time elapsed: 0.091 s
% 0.20/0.52  % (5057)------------------------------
% 0.20/0.52  % (5057)------------------------------
% 0.20/0.52  % (5058)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (5044)Success in time 0.161 s
%------------------------------------------------------------------------------

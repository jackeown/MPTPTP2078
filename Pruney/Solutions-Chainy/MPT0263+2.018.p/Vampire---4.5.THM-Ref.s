%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:14 EST 2020

% Result     : Theorem 2.76s
% Output     : Refutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   64 (  94 expanded)
%              Number of leaves         :   14 (  26 expanded)
%              Depth                    :   17
%              Number of atoms          :  255 ( 499 expanded)
%              Number of equality atoms :  107 ( 145 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1087,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f211,f1086])).

fof(f1086,plain,
    ( spl4_2
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f1085])).

fof(f1085,plain,
    ( $false
    | spl4_2
    | spl4_7 ),
    inference(subsumption_resolution,[],[f1083,f210])).

fof(f210,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl4_7
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1083,plain,
    ( r2_hidden(sK0,sK1)
    | spl4_2 ),
    inference(resolution,[],[f1064,f68])).

fof(f68,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_2
  <=> r1_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1064,plain,(
    ! [X23,X22] :
      ( r1_xboole_0(k1_tarski(X22),X23)
      | r2_hidden(X22,X23) ) ),
    inference(trivial_inequality_removal,[],[f1043])).

fof(f1043,plain,(
    ! [X23,X22] :
      ( k1_tarski(X22) != k1_tarski(X22)
      | r1_xboole_0(k1_tarski(X22),X23)
      | r2_hidden(X22,X23) ) ),
    inference(superposition,[],[f46,f1024])).

fof(f1024,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f1013])).

fof(f1013,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(superposition,[],[f256,f253])).

fof(f253,plain,(
    ! [X26,X27] :
      ( sK2(k1_tarski(X26),X27,k1_tarski(X26)) = X26
      | k1_tarski(X26) = k4_xboole_0(k1_tarski(X26),X27) ) ),
    inference(resolution,[],[f128,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1
      | X0 = X1 ) ),
    inference(superposition,[],[f59,f45])).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f128,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f256,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK2(X1,X2,X1),X2)
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(subsumption_resolution,[],[f254,f34])).

fof(f254,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = X1
      | r2_hidden(sK2(X1,X2,X1),X2)
      | ~ r2_hidden(sK2(X1,X2,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f243])).

fof(f243,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = X1
      | r2_hidden(sK2(X1,X2,X1),X2)
      | ~ r2_hidden(sK2(X1,X2,X1),X1)
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f128,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f211,plain,
    ( ~ spl4_7
    | spl4_1 ),
    inference(avatar_split_clause,[],[f206,f61,f208])).

fof(f61,plain,
    ( spl4_1
  <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f206,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f198])).

fof(f198,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | ~ r2_hidden(sK0,sK1)
    | spl4_1 ),
    inference(superposition,[],[f63,f103])).

fof(f103,plain,(
    ! [X4,X3] :
      ( k1_tarski(X3) = k3_xboole_0(k1_tarski(X3),X4)
      | ~ r2_hidden(X3,X4) ) ),
    inference(forward_demodulation,[],[f96,f49])).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f96,plain,(
    ! [X4,X3] :
      ( k3_xboole_0(k1_tarski(X3),X4) = k4_xboole_0(k1_tarski(X3),k1_xboole_0)
      | ~ r2_hidden(X3,X4) ) ),
    inference(superposition,[],[f43,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f63,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f69,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f64,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:58:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.32/0.56  % (31336)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.55/0.56  % (31354)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.55/0.58  % (31345)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.55/0.58  % (31342)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.55/0.58  % (31345)Refutation not found, incomplete strategy% (31345)------------------------------
% 1.55/0.58  % (31345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (31345)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (31345)Memory used [KB]: 1663
% 1.55/0.58  % (31345)Time elapsed: 0.148 s
% 1.55/0.58  % (31345)------------------------------
% 1.55/0.58  % (31345)------------------------------
% 1.55/0.58  % (31332)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.55/0.58  % (31332)Refutation not found, incomplete strategy% (31332)------------------------------
% 1.55/0.58  % (31332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (31332)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (31332)Memory used [KB]: 1663
% 1.55/0.58  % (31332)Time elapsed: 0.160 s
% 1.55/0.58  % (31332)------------------------------
% 1.55/0.58  % (31332)------------------------------
% 1.55/0.59  % (31346)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.55/0.59  % (31339)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.55/0.59  % (31334)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.55/0.59  % (31331)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.55/0.60  % (31333)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.55/0.60  % (31347)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.55/0.60  % (31356)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.55/0.61  % (31335)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.55/0.61  % (31355)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.55/0.61  % (31348)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.55/0.61  % (31356)Refutation not found, incomplete strategy% (31356)------------------------------
% 1.55/0.61  % (31356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.61  % (31347)Refutation not found, incomplete strategy% (31347)------------------------------
% 1.55/0.61  % (31347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.61  % (31347)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.61  
% 1.55/0.61  % (31347)Memory used [KB]: 10618
% 1.55/0.61  % (31347)Time elapsed: 0.172 s
% 1.55/0.61  % (31347)------------------------------
% 1.55/0.61  % (31347)------------------------------
% 1.55/0.61  % (31356)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.61  
% 1.55/0.61  % (31356)Memory used [KB]: 10618
% 1.55/0.61  % (31356)Time elapsed: 0.175 s
% 1.55/0.61  % (31356)------------------------------
% 1.55/0.61  % (31356)------------------------------
% 1.55/0.61  % (31340)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.55/0.62  % (31359)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.55/0.62  % (31359)Refutation not found, incomplete strategy% (31359)------------------------------
% 1.55/0.62  % (31359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.62  % (31359)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.62  
% 1.55/0.62  % (31359)Memory used [KB]: 6140
% 1.55/0.62  % (31359)Time elapsed: 0.190 s
% 1.55/0.62  % (31359)------------------------------
% 1.55/0.62  % (31359)------------------------------
% 1.55/0.62  % (31351)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.55/0.62  % (31352)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.55/0.62  % (31357)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.55/0.62  % (31337)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.63  % (31361)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.55/0.63  % (31338)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.55/0.63  % (31361)Refutation not found, incomplete strategy% (31361)------------------------------
% 1.55/0.63  % (31361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.63  % (31361)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.63  
% 1.55/0.63  % (31361)Memory used [KB]: 1663
% 1.55/0.63  % (31361)Time elapsed: 0.197 s
% 1.55/0.63  % (31361)------------------------------
% 1.55/0.63  % (31361)------------------------------
% 1.55/0.63  % (31349)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.55/0.63  % (31360)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.55/0.63  % (31358)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.55/0.63  % (31349)Refutation not found, incomplete strategy% (31349)------------------------------
% 1.55/0.63  % (31349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.63  % (31349)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.63  
% 1.55/0.63  % (31349)Memory used [KB]: 1663
% 1.55/0.63  % (31349)Time elapsed: 0.203 s
% 1.55/0.63  % (31349)------------------------------
% 1.55/0.63  % (31349)------------------------------
% 1.55/0.63  % (31348)Refutation not found, incomplete strategy% (31348)------------------------------
% 1.55/0.63  % (31348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.63  % (31348)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.63  
% 1.55/0.63  % (31348)Memory used [KB]: 1663
% 1.55/0.63  % (31348)Time elapsed: 0.198 s
% 1.55/0.63  % (31348)------------------------------
% 1.55/0.63  % (31348)------------------------------
% 1.55/0.63  % (31358)Refutation not found, incomplete strategy% (31358)------------------------------
% 1.55/0.63  % (31358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.63  % (31358)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.63  
% 1.55/0.63  % (31358)Memory used [KB]: 6140
% 1.55/0.63  % (31358)Time elapsed: 0.196 s
% 1.55/0.63  % (31358)------------------------------
% 1.55/0.63  % (31358)------------------------------
% 1.55/0.63  % (31343)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.55/0.63  % (31344)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.55/0.63  % (31343)Refutation not found, incomplete strategy% (31343)------------------------------
% 1.55/0.63  % (31343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.63  % (31343)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.63  
% 1.55/0.63  % (31343)Memory used [KB]: 10618
% 1.55/0.63  % (31343)Time elapsed: 0.209 s
% 1.55/0.63  % (31343)------------------------------
% 1.55/0.63  % (31343)------------------------------
% 1.55/0.64  % (31341)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.55/0.64  % (31350)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 2.76/0.75  % (31352)Refutation found. Thanks to Tanya!
% 2.76/0.75  % SZS status Theorem for theBenchmark
% 2.76/0.75  % SZS output start Proof for theBenchmark
% 2.76/0.75  fof(f1087,plain,(
% 2.76/0.75    $false),
% 2.76/0.75    inference(avatar_sat_refutation,[],[f64,f69,f211,f1086])).
% 2.76/0.75  fof(f1086,plain,(
% 2.76/0.75    spl4_2 | spl4_7),
% 2.76/0.75    inference(avatar_contradiction_clause,[],[f1085])).
% 2.76/0.75  fof(f1085,plain,(
% 2.76/0.75    $false | (spl4_2 | spl4_7)),
% 2.76/0.75    inference(subsumption_resolution,[],[f1083,f210])).
% 2.76/0.75  fof(f210,plain,(
% 2.76/0.75    ~r2_hidden(sK0,sK1) | spl4_7),
% 2.76/0.75    inference(avatar_component_clause,[],[f208])).
% 2.76/0.75  fof(f208,plain,(
% 2.76/0.75    spl4_7 <=> r2_hidden(sK0,sK1)),
% 2.76/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.76/0.75  fof(f1083,plain,(
% 2.76/0.75    r2_hidden(sK0,sK1) | spl4_2),
% 2.76/0.75    inference(resolution,[],[f1064,f68])).
% 2.76/0.75  fof(f68,plain,(
% 2.76/0.75    ~r1_xboole_0(k1_tarski(sK0),sK1) | spl4_2),
% 2.76/0.75    inference(avatar_component_clause,[],[f66])).
% 2.76/0.75  fof(f66,plain,(
% 2.76/0.75    spl4_2 <=> r1_xboole_0(k1_tarski(sK0),sK1)),
% 2.76/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.76/0.75  fof(f1064,plain,(
% 2.76/0.75    ( ! [X23,X22] : (r1_xboole_0(k1_tarski(X22),X23) | r2_hidden(X22,X23)) )),
% 2.76/0.75    inference(trivial_inequality_removal,[],[f1043])).
% 2.76/0.75  fof(f1043,plain,(
% 2.76/0.75    ( ! [X23,X22] : (k1_tarski(X22) != k1_tarski(X22) | r1_xboole_0(k1_tarski(X22),X23) | r2_hidden(X22,X23)) )),
% 2.76/0.75    inference(superposition,[],[f46,f1024])).
% 2.76/0.75  fof(f1024,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.76/0.75    inference(duplicate_literal_removal,[],[f1013])).
% 2.76/0.75  fof(f1013,plain,(
% 2.76/0.75    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 2.76/0.75    inference(superposition,[],[f256,f253])).
% 2.76/0.75  fof(f253,plain,(
% 2.76/0.75    ( ! [X26,X27] : (sK2(k1_tarski(X26),X27,k1_tarski(X26)) = X26 | k1_tarski(X26) = k4_xboole_0(k1_tarski(X26),X27)) )),
% 2.76/0.75    inference(resolution,[],[f128,f123])).
% 2.76/0.75  fof(f123,plain,(
% 2.76/0.75    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1) )),
% 2.76/0.75    inference(duplicate_literal_removal,[],[f122])).
% 2.76/0.75  fof(f122,plain,(
% 2.76/0.75    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1 | X0 = X1) )),
% 2.76/0.75    inference(superposition,[],[f59,f45])).
% 2.76/0.75  fof(f45,plain,(
% 2.76/0.75    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f7])).
% 2.76/0.75  fof(f7,axiom,(
% 2.76/0.75    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.76/0.75  fof(f59,plain,(
% 2.76/0.75    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 2.76/0.75    inference(equality_resolution,[],[f37])).
% 2.76/0.75  fof(f37,plain,(
% 2.76/0.75    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.76/0.75    inference(cnf_transformation,[],[f27])).
% 2.76/0.75  fof(f27,plain,(
% 2.76/0.75    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.76/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 2.76/0.75  fof(f26,plain,(
% 2.76/0.75    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.76/0.75    introduced(choice_axiom,[])).
% 2.76/0.75  fof(f25,plain,(
% 2.76/0.75    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.76/0.75    inference(rectify,[],[f24])).
% 2.76/0.75  fof(f24,plain,(
% 2.76/0.75    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.76/0.75    inference(flattening,[],[f23])).
% 2.76/0.75  fof(f23,plain,(
% 2.76/0.75    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.76/0.75    inference(nnf_transformation,[],[f6])).
% 2.76/0.75  fof(f6,axiom,(
% 2.76/0.75    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.76/0.75  fof(f128,plain,(
% 2.76/0.75    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 2.76/0.75    inference(factoring,[],[f34])).
% 2.76/0.75  fof(f34,plain,(
% 2.76/0.75    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 2.76/0.75    inference(cnf_transformation,[],[f22])).
% 2.76/0.75  fof(f22,plain,(
% 2.76/0.75    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.76/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 2.76/0.75  fof(f21,plain,(
% 2.76/0.75    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.76/0.75    introduced(choice_axiom,[])).
% 2.76/0.75  fof(f20,plain,(
% 2.76/0.75    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.76/0.75    inference(rectify,[],[f19])).
% 2.76/0.75  fof(f19,plain,(
% 2.76/0.75    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.76/0.75    inference(flattening,[],[f18])).
% 2.76/0.75  fof(f18,plain,(
% 2.76/0.75    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.76/0.75    inference(nnf_transformation,[],[f2])).
% 2.76/0.75  fof(f2,axiom,(
% 2.76/0.75    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.76/0.75  fof(f256,plain,(
% 2.76/0.75    ( ! [X2,X1] : (r2_hidden(sK2(X1,X2,X1),X2) | k4_xboole_0(X1,X2) = X1) )),
% 2.76/0.75    inference(subsumption_resolution,[],[f254,f34])).
% 2.76/0.75  fof(f254,plain,(
% 2.76/0.75    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK2(X1,X2,X1),X2) | ~r2_hidden(sK2(X1,X2,X1),X1)) )),
% 2.76/0.75    inference(duplicate_literal_removal,[],[f243])).
% 2.76/0.75  fof(f243,plain,(
% 2.76/0.75    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK2(X1,X2,X1),X2) | ~r2_hidden(sK2(X1,X2,X1),X1) | k4_xboole_0(X1,X2) = X1) )),
% 2.76/0.75    inference(resolution,[],[f128,f36])).
% 2.76/0.75  fof(f36,plain,(
% 2.76/0.75    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 2.76/0.75    inference(cnf_transformation,[],[f22])).
% 2.76/0.75  fof(f46,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f15])).
% 2.76/0.75  fof(f15,plain,(
% 2.76/0.75    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 2.76/0.75    inference(ennf_transformation,[],[f13])).
% 2.76/0.75  fof(f13,plain,(
% 2.76/0.75    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 2.76/0.75    inference(unused_predicate_definition_removal,[],[f5])).
% 2.76/0.75  fof(f5,axiom,(
% 2.76/0.75    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.76/0.75  fof(f211,plain,(
% 2.76/0.75    ~spl4_7 | spl4_1),
% 2.76/0.75    inference(avatar_split_clause,[],[f206,f61,f208])).
% 2.76/0.75  fof(f61,plain,(
% 2.76/0.75    spl4_1 <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 2.76/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.76/0.75  fof(f206,plain,(
% 2.76/0.75    ~r2_hidden(sK0,sK1) | spl4_1),
% 2.76/0.75    inference(trivial_inequality_removal,[],[f198])).
% 2.76/0.75  fof(f198,plain,(
% 2.76/0.75    k1_tarski(sK0) != k1_tarski(sK0) | ~r2_hidden(sK0,sK1) | spl4_1),
% 2.76/0.75    inference(superposition,[],[f63,f103])).
% 2.76/0.75  fof(f103,plain,(
% 2.76/0.75    ( ! [X4,X3] : (k1_tarski(X3) = k3_xboole_0(k1_tarski(X3),X4) | ~r2_hidden(X3,X4)) )),
% 2.76/0.75    inference(forward_demodulation,[],[f96,f49])).
% 2.76/0.75  fof(f49,plain,(
% 2.76/0.75    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.76/0.75    inference(cnf_transformation,[],[f3])).
% 2.76/0.75  fof(f3,axiom,(
% 2.76/0.75    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.76/0.75  fof(f96,plain,(
% 2.76/0.75    ( ! [X4,X3] : (k3_xboole_0(k1_tarski(X3),X4) = k4_xboole_0(k1_tarski(X3),k1_xboole_0) | ~r2_hidden(X3,X4)) )),
% 2.76/0.75    inference(superposition,[],[f43,f48])).
% 2.76/0.75  fof(f48,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f28])).
% 2.76/0.75  fof(f28,plain,(
% 2.76/0.75    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 2.76/0.75    inference(nnf_transformation,[],[f10])).
% 2.76/0.75  fof(f10,axiom,(
% 2.76/0.75    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 2.76/0.75  fof(f43,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.76/0.75    inference(cnf_transformation,[],[f4])).
% 2.76/0.75  fof(f4,axiom,(
% 2.76/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.76/0.75  fof(f63,plain,(
% 2.76/0.75    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) | spl4_1),
% 2.76/0.75    inference(avatar_component_clause,[],[f61])).
% 2.76/0.75  fof(f69,plain,(
% 2.76/0.75    ~spl4_2),
% 2.76/0.75    inference(avatar_split_clause,[],[f29,f66])).
% 2.76/0.75  fof(f29,plain,(
% 2.76/0.75    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 2.76/0.75    inference(cnf_transformation,[],[f17])).
% 2.76/0.75  fof(f17,plain,(
% 2.76/0.75    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 2.76/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).
% 2.76/0.75  fof(f16,plain,(
% 2.76/0.75    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 2.76/0.75    introduced(choice_axiom,[])).
% 2.76/0.75  fof(f14,plain,(
% 2.76/0.75    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 2.76/0.75    inference(ennf_transformation,[],[f12])).
% 2.76/0.75  fof(f12,negated_conjecture,(
% 2.76/0.75    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 2.76/0.75    inference(negated_conjecture,[],[f11])).
% 2.76/0.75  fof(f11,conjecture,(
% 2.76/0.75    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 2.76/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 2.76/0.75  fof(f64,plain,(
% 2.76/0.75    ~spl4_1),
% 2.76/0.75    inference(avatar_split_clause,[],[f30,f61])).
% 2.76/0.75  fof(f30,plain,(
% 2.76/0.75    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 2.76/0.75    inference(cnf_transformation,[],[f17])).
% 2.76/0.75  % SZS output end Proof for theBenchmark
% 2.76/0.75  % (31352)------------------------------
% 2.76/0.75  % (31352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.76/0.75  % (31352)Termination reason: Refutation
% 2.76/0.75  
% 2.76/0.75  % (31352)Memory used [KB]: 6908
% 2.76/0.75  % (31352)Time elapsed: 0.323 s
% 2.76/0.75  % (31352)------------------------------
% 2.76/0.75  % (31352)------------------------------
% 2.76/0.75  % (31398)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.76/0.77  % (31330)Success in time 0.399 s
%------------------------------------------------------------------------------

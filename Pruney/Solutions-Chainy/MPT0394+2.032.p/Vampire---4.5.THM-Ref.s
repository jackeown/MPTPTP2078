%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:00 EST 2020

% Result     : Theorem 2.29s
% Output     : Refutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 135 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  223 ( 538 expanded)
%              Number of equality atoms :   74 ( 151 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3088,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f67,f1697,f2831,f2978,f3085])).

fof(f3085,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_37 ),
    inference(avatar_contradiction_clause,[],[f3084])).

fof(f3084,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f3065,f3056])).

fof(f3056,plain,
    ( ! [X0] : sK1 = X0
    | ~ spl4_3
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f3052,f162])).

fof(f162,plain,
    ( ! [X11] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X11)
    | ~ spl4_3 ),
    inference(resolution,[],[f112,f66])).

fof(f66,plain,
    ( ! [X4] : ~ r2_hidden(X4,k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_3
  <=> ! [X4] : ~ r2_hidden(X4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f3052,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_tarski(X0))
        | sK1 = X0 )
    | ~ spl4_37 ),
    inference(superposition,[],[f39,f2830])).

fof(f2830,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f2828])).

fof(f2828,plain,
    ( spl4_37
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f3065,plain,
    ( sK1 != k1_setfam_1(k2_tarski(sK0,sK1))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_37 ),
    inference(backward_demodulation,[],[f52,f3056])).

fof(f52,plain,
    ( k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_1
  <=> k3_xboole_0(sK0,sK1) = k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f2978,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_36 ),
    inference(avatar_contradiction_clause,[],[f2977])).

fof(f2977,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f2903,f2842])).

fof(f2842,plain,
    ( ! [X0] : sK0 = X0
    | ~ spl4_3
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f2832,f162])).

fof(f2832,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_tarski(X0))
        | sK0 = X0 )
    | ~ spl4_36 ),
    inference(superposition,[],[f39,f2826])).

fof(f2826,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f2824])).

fof(f2824,plain,
    ( spl4_36
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f2903,plain,
    ( sK0 != k1_setfam_1(k2_tarski(sK0,sK1))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_36 ),
    inference(backward_demodulation,[],[f52,f2842])).

fof(f2831,plain,
    ( spl4_36
    | spl4_37
    | spl4_1 ),
    inference(avatar_split_clause,[],[f2820,f50,f2828,f2824])).

fof(f2820,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | k1_xboole_0 = k1_tarski(sK0)
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f2815])).

fof(f2815,plain,
    ( k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1)
    | k1_xboole_0 = k1_tarski(sK1)
    | k1_xboole_0 = k1_tarski(sK0)
    | spl4_1 ),
    inference(superposition,[],[f52,f233])).

fof(f233,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))
      | k1_xboole_0 = k1_tarski(X1)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(forward_demodulation,[],[f222,f43])).

fof(f43,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f222,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,k1_setfam_1(k1_tarski(X1)))
      | k1_xboole_0 = k1_tarski(X1)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f94,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f94,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f36,f43])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f1697,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f1684])).

fof(f1684,plain,
    ( $false
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f41,f63,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f63,plain,
    ( ! [X2,X3] : ~ r1_xboole_0(X2,X3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_2
  <=> ! [X3,X2] : ~ r1_xboole_0(X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f67,plain,
    ( spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f60,f65,f62])).

fof(f60,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ r1_xboole_0(X2,X3)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f45,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f53,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f29,f50])).

fof(f29,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f19])).

fof(f19,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (30954)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.50  % (30949)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.50  % (30938)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.50  % (30950)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.50  % (30941)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.50  % (30931)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.50  % (30941)Refutation not found, incomplete strategy% (30941)------------------------------
% 0.20/0.50  % (30941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (30941)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (30941)Memory used [KB]: 1663
% 0.20/0.50  % (30941)Time elapsed: 0.058 s
% 0.20/0.50  % (30941)------------------------------
% 0.20/0.50  % (30941)------------------------------
% 0.20/0.50  % (30932)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (30933)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (30942)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (30930)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (30929)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (30955)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.51  % (30955)Refutation not found, incomplete strategy% (30955)------------------------------
% 0.20/0.51  % (30955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (30955)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (30955)Memory used [KB]: 10618
% 0.20/0.51  % (30955)Time elapsed: 0.113 s
% 0.20/0.51  % (30946)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (30934)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (30927)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (30947)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (30928)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (30939)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (30936)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (30939)Refutation not found, incomplete strategy% (30939)------------------------------
% 0.20/0.52  % (30939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (30954)Refutation not found, incomplete strategy% (30954)------------------------------
% 0.20/0.52  % (30954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (30954)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (30954)Memory used [KB]: 6140
% 0.20/0.52  % (30954)Time elapsed: 0.113 s
% 0.20/0.52  % (30954)------------------------------
% 0.20/0.52  % (30954)------------------------------
% 0.20/0.53  % (30951)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (30940)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (30951)Refutation not found, incomplete strategy% (30951)------------------------------
% 0.20/0.53  % (30951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (30951)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (30951)Memory used [KB]: 10618
% 0.20/0.53  % (30951)Time elapsed: 0.131 s
% 0.20/0.53  % (30951)------------------------------
% 0.20/0.53  % (30951)------------------------------
% 0.20/0.53  % (30928)Refutation not found, incomplete strategy% (30928)------------------------------
% 0.20/0.53  % (30928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (30928)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (30928)Memory used [KB]: 1663
% 0.20/0.53  % (30928)Time elapsed: 0.128 s
% 0.20/0.53  % (30928)------------------------------
% 0.20/0.53  % (30928)------------------------------
% 1.35/0.53  % (30939)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (30939)Memory used [KB]: 10618
% 1.35/0.53  % (30939)Time elapsed: 0.126 s
% 1.35/0.53  % (30939)------------------------------
% 1.35/0.53  % (30939)------------------------------
% 1.35/0.53  % (30953)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.35/0.53  % (30953)Refutation not found, incomplete strategy% (30953)------------------------------
% 1.35/0.53  % (30953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (30953)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (30953)Memory used [KB]: 6140
% 1.35/0.53  % (30953)Time elapsed: 0.130 s
% 1.35/0.53  % (30953)------------------------------
% 1.35/0.53  % (30953)------------------------------
% 1.35/0.53  % (30935)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.35/0.53  % (30952)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.35/0.53  % (30945)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.35/0.53  % (30945)Refutation not found, incomplete strategy% (30945)------------------------------
% 1.35/0.53  % (30945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (30945)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (30945)Memory used [KB]: 1663
% 1.35/0.53  % (30945)Time elapsed: 0.130 s
% 1.35/0.53  % (30945)------------------------------
% 1.35/0.53  % (30945)------------------------------
% 1.35/0.53  % (30956)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.35/0.53  % (30956)Refutation not found, incomplete strategy% (30956)------------------------------
% 1.35/0.53  % (30956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (30956)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (30956)Memory used [KB]: 1663
% 1.35/0.53  % (30956)Time elapsed: 0.001 s
% 1.35/0.53  % (30956)------------------------------
% 1.35/0.53  % (30956)------------------------------
% 1.35/0.54  % (30955)------------------------------
% 1.35/0.54  % (30955)------------------------------
% 1.35/0.54  % (30948)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.35/0.54  % (30944)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.35/0.54  % (30944)Refutation not found, incomplete strategy% (30944)------------------------------
% 1.35/0.54  % (30944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (30944)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (30944)Memory used [KB]: 1663
% 1.35/0.54  % (30944)Time elapsed: 0.141 s
% 1.35/0.54  % (30944)------------------------------
% 1.35/0.54  % (30944)------------------------------
% 1.35/0.54  % (30937)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.35/0.54  % (30937)Refutation not found, incomplete strategy% (30937)------------------------------
% 1.35/0.54  % (30937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (30937)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (30937)Memory used [KB]: 10618
% 1.35/0.54  % (30937)Time elapsed: 0.141 s
% 1.35/0.54  % (30937)------------------------------
% 1.35/0.54  % (30937)------------------------------
% 1.35/0.54  % (30943)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.35/0.54  % (30943)Refutation not found, incomplete strategy% (30943)------------------------------
% 1.35/0.54  % (30943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (30943)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (30943)Memory used [KB]: 10618
% 1.35/0.54  % (30943)Time elapsed: 0.138 s
% 1.35/0.54  % (30943)------------------------------
% 1.35/0.54  % (30943)------------------------------
% 1.96/0.64  % (30930)Refutation not found, incomplete strategy% (30930)------------------------------
% 1.96/0.64  % (30930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.64  % (30930)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.64  
% 1.96/0.64  % (30930)Memory used [KB]: 6140
% 1.96/0.64  % (30930)Time elapsed: 0.228 s
% 1.96/0.64  % (30930)------------------------------
% 1.96/0.64  % (30930)------------------------------
% 1.96/0.64  % (30942)Refutation not found, incomplete strategy% (30942)------------------------------
% 1.96/0.64  % (30942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.64  % (30942)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.64  
% 1.96/0.64  % (30942)Memory used [KB]: 6140
% 1.96/0.64  % (30942)Time elapsed: 0.222 s
% 1.96/0.64  % (30942)------------------------------
% 1.96/0.64  % (30942)------------------------------
% 1.96/0.65  % (30957)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.96/0.65  % (30959)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.96/0.65  % (30959)Refutation not found, incomplete strategy% (30959)------------------------------
% 1.96/0.65  % (30959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.65  % (30959)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.65  
% 1.96/0.65  % (30959)Memory used [KB]: 6140
% 1.96/0.65  % (30959)Time elapsed: 0.096 s
% 1.96/0.65  % (30959)------------------------------
% 1.96/0.65  % (30959)------------------------------
% 1.96/0.66  % (30962)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 1.96/0.66  % (30962)Refutation not found, incomplete strategy% (30962)------------------------------
% 1.96/0.66  % (30962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.66  % (30962)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.66  
% 1.96/0.66  % (30962)Memory used [KB]: 1663
% 1.96/0.66  % (30962)Time elapsed: 0.106 s
% 1.96/0.66  % (30962)------------------------------
% 1.96/0.66  % (30962)------------------------------
% 1.96/0.66  % (30961)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 1.96/0.66  % (30927)Refutation not found, incomplete strategy% (30927)------------------------------
% 1.96/0.66  % (30927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.66  % (30927)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.66  
% 1.96/0.66  % (30927)Memory used [KB]: 1663
% 1.96/0.66  % (30927)Time elapsed: 0.246 s
% 1.96/0.66  % (30927)------------------------------
% 1.96/0.66  % (30927)------------------------------
% 1.96/0.66  % (30961)Refutation not found, incomplete strategy% (30961)------------------------------
% 1.96/0.66  % (30961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.66  % (30961)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.66  
% 1.96/0.66  % (30961)Memory used [KB]: 10618
% 1.96/0.66  % (30961)Time elapsed: 0.107 s
% 1.96/0.66  % (30961)------------------------------
% 1.96/0.66  % (30961)------------------------------
% 1.96/0.66  % (30958)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.96/0.67  % (30963)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 1.96/0.67  % (30964)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 1.96/0.67  % (30967)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 1.96/0.68  % (30966)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.29/0.68  % (30966)Refutation not found, incomplete strategy% (30966)------------------------------
% 2.29/0.68  % (30966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.68  % (30966)Termination reason: Refutation not found, incomplete strategy
% 2.29/0.68  
% 2.29/0.68  % (30966)Memory used [KB]: 10618
% 2.29/0.68  % (30966)Time elapsed: 0.121 s
% 2.29/0.68  % (30966)------------------------------
% 2.29/0.68  % (30966)------------------------------
% 2.29/0.68  % (30960)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.29/0.68  % (30968)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.29/0.68  % (30965)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.29/0.71  % (30948)Refutation found. Thanks to Tanya!
% 2.29/0.71  % SZS status Theorem for theBenchmark
% 2.29/0.71  % SZS output start Proof for theBenchmark
% 2.29/0.71  fof(f3088,plain,(
% 2.29/0.71    $false),
% 2.29/0.71    inference(avatar_sat_refutation,[],[f53,f67,f1697,f2831,f2978,f3085])).
% 2.29/0.71  fof(f3085,plain,(
% 2.29/0.71    spl4_1 | ~spl4_3 | ~spl4_37),
% 2.29/0.71    inference(avatar_contradiction_clause,[],[f3084])).
% 2.29/0.71  fof(f3084,plain,(
% 2.29/0.71    $false | (spl4_1 | ~spl4_3 | ~spl4_37)),
% 2.29/0.71    inference(subsumption_resolution,[],[f3065,f3056])).
% 2.29/0.71  fof(f3056,plain,(
% 2.29/0.71    ( ! [X0] : (sK1 = X0) ) | (~spl4_3 | ~spl4_37)),
% 2.29/0.71    inference(subsumption_resolution,[],[f3052,f162])).
% 2.29/0.71  fof(f162,plain,(
% 2.29/0.71    ( ! [X11] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X11)) ) | ~spl4_3),
% 2.29/0.71    inference(resolution,[],[f112,f66])).
% 2.29/0.71  fof(f66,plain,(
% 2.29/0.71    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) ) | ~spl4_3),
% 2.29/0.71    inference(avatar_component_clause,[],[f65])).
% 2.29/0.71  fof(f65,plain,(
% 2.29/0.71    spl4_3 <=> ! [X4] : ~r2_hidden(X4,k1_xboole_0)),
% 2.29/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.29/0.71  fof(f112,plain,(
% 2.29/0.71    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k3_xboole_0(X0,X1) = X0) )),
% 2.29/0.71    inference(factoring,[],[f33])).
% 2.29/0.71  fof(f33,plain,(
% 2.29/0.71    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 2.29/0.71    inference(cnf_transformation,[],[f25])).
% 2.29/0.71  fof(f25,plain,(
% 2.29/0.71    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.29/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).
% 2.29/0.71  fof(f24,plain,(
% 2.29/0.71    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.29/0.71    introduced(choice_axiom,[])).
% 2.29/0.71  fof(f23,plain,(
% 2.29/0.71    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.29/0.71    inference(rectify,[],[f22])).
% 2.29/0.71  fof(f22,plain,(
% 2.29/0.71    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.29/0.71    inference(flattening,[],[f21])).
% 2.29/0.71  fof(f21,plain,(
% 2.29/0.71    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.29/0.71    inference(nnf_transformation,[],[f1])).
% 2.29/0.71  fof(f1,axiom,(
% 2.29/0.71    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.29/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.29/0.71  fof(f3052,plain,(
% 2.29/0.71    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_tarski(X0)) | sK1 = X0) ) | ~spl4_37),
% 2.29/0.71    inference(superposition,[],[f39,f2830])).
% 2.29/0.71  fof(f2830,plain,(
% 2.29/0.71    k1_xboole_0 = k1_tarski(sK1) | ~spl4_37),
% 2.29/0.71    inference(avatar_component_clause,[],[f2828])).
% 2.29/0.71  fof(f2828,plain,(
% 2.29/0.71    spl4_37 <=> k1_xboole_0 = k1_tarski(sK1)),
% 2.29/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 2.29/0.71  fof(f39,plain,(
% 2.29/0.71    ( ! [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 2.29/0.71    inference(cnf_transformation,[],[f17])).
% 2.29/0.71  fof(f17,plain,(
% 2.29/0.71    ! [X0,X1] : (X0 = X1 | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 2.29/0.71    inference(ennf_transformation,[],[f8])).
% 2.29/0.71  fof(f8,axiom,(
% 2.29/0.71    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.29/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 2.29/0.71  fof(f3065,plain,(
% 2.29/0.71    sK1 != k1_setfam_1(k2_tarski(sK0,sK1)) | (spl4_1 | ~spl4_3 | ~spl4_37)),
% 2.29/0.71    inference(backward_demodulation,[],[f52,f3056])).
% 2.29/0.71  fof(f52,plain,(
% 2.29/0.71    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) | spl4_1),
% 2.29/0.71    inference(avatar_component_clause,[],[f50])).
% 2.29/0.71  fof(f50,plain,(
% 2.29/0.71    spl4_1 <=> k3_xboole_0(sK0,sK1) = k1_setfam_1(k2_tarski(sK0,sK1))),
% 2.29/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.29/0.71  fof(f2978,plain,(
% 2.29/0.71    spl4_1 | ~spl4_3 | ~spl4_36),
% 2.29/0.71    inference(avatar_contradiction_clause,[],[f2977])).
% 2.29/0.71  fof(f2977,plain,(
% 2.29/0.71    $false | (spl4_1 | ~spl4_3 | ~spl4_36)),
% 2.29/0.71    inference(subsumption_resolution,[],[f2903,f2842])).
% 2.29/0.71  fof(f2842,plain,(
% 2.29/0.71    ( ! [X0] : (sK0 = X0) ) | (~spl4_3 | ~spl4_36)),
% 2.29/0.71    inference(subsumption_resolution,[],[f2832,f162])).
% 2.29/0.71  fof(f2832,plain,(
% 2.29/0.71    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_tarski(X0)) | sK0 = X0) ) | ~spl4_36),
% 2.29/0.71    inference(superposition,[],[f39,f2826])).
% 2.29/0.71  fof(f2826,plain,(
% 2.29/0.71    k1_xboole_0 = k1_tarski(sK0) | ~spl4_36),
% 2.29/0.71    inference(avatar_component_clause,[],[f2824])).
% 2.29/0.71  fof(f2824,plain,(
% 2.29/0.71    spl4_36 <=> k1_xboole_0 = k1_tarski(sK0)),
% 2.29/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 2.29/0.71  fof(f2903,plain,(
% 2.29/0.71    sK0 != k1_setfam_1(k2_tarski(sK0,sK1)) | (spl4_1 | ~spl4_3 | ~spl4_36)),
% 2.29/0.71    inference(backward_demodulation,[],[f52,f2842])).
% 2.29/0.71  fof(f2831,plain,(
% 2.29/0.71    spl4_36 | spl4_37 | spl4_1),
% 2.29/0.71    inference(avatar_split_clause,[],[f2820,f50,f2828,f2824])).
% 2.29/0.71  fof(f2820,plain,(
% 2.29/0.71    k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = k1_tarski(sK0) | spl4_1),
% 2.29/0.71    inference(trivial_inequality_removal,[],[f2815])).
% 2.29/0.71  fof(f2815,plain,(
% 2.29/0.71    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1) | k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = k1_tarski(sK0) | spl4_1),
% 2.29/0.71    inference(superposition,[],[f52,f233])).
% 2.29/0.71  fof(f233,plain,(
% 2.29/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) | k1_xboole_0 = k1_tarski(X1) | k1_xboole_0 = k1_tarski(X0)) )),
% 2.29/0.71    inference(forward_demodulation,[],[f222,f43])).
% 2.29/0.71  fof(f43,plain,(
% 2.29/0.71    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 2.29/0.71    inference(cnf_transformation,[],[f10])).
% 2.29/0.71  fof(f10,axiom,(
% 2.29/0.71    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.29/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 2.29/0.71  fof(f222,plain,(
% 2.29/0.71    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,k1_setfam_1(k1_tarski(X1))) | k1_xboole_0 = k1_tarski(X1) | k1_xboole_0 = k1_tarski(X0)) )),
% 2.29/0.71    inference(superposition,[],[f94,f40])).
% 2.29/0.71  fof(f40,plain,(
% 2.29/0.71    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.29/0.71    inference(cnf_transformation,[],[f6])).
% 2.29/0.71  fof(f6,axiom,(
% 2.29/0.71    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 2.29/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 2.29/0.71  fof(f94,plain,(
% 2.29/0.71    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = k1_tarski(X0)) )),
% 2.29/0.71    inference(superposition,[],[f36,f43])).
% 2.29/0.71  fof(f36,plain,(
% 2.29/0.71    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.29/0.71    inference(cnf_transformation,[],[f16])).
% 2.29/0.71  fof(f16,plain,(
% 2.29/0.71    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.29/0.71    inference(ennf_transformation,[],[f9])).
% 2.29/0.71  fof(f9,axiom,(
% 2.29/0.71    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.29/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).
% 2.29/0.71  fof(f1697,plain,(
% 2.29/0.71    ~spl4_2),
% 2.29/0.71    inference(avatar_contradiction_clause,[],[f1684])).
% 2.29/0.71  fof(f1684,plain,(
% 2.29/0.71    $false | ~spl4_2),
% 2.29/0.71    inference(unit_resulting_resolution,[],[f41,f63,f38])).
% 2.29/0.71  fof(f38,plain,(
% 2.29/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 2.29/0.71    inference(cnf_transformation,[],[f26])).
% 2.29/0.71  fof(f26,plain,(
% 2.29/0.71    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.29/0.71    inference(nnf_transformation,[],[f2])).
% 2.29/0.71  fof(f2,axiom,(
% 2.29/0.71    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.29/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.29/0.71  fof(f63,plain,(
% 2.29/0.71    ( ! [X2,X3] : (~r1_xboole_0(X2,X3)) ) | ~spl4_2),
% 2.29/0.71    inference(avatar_component_clause,[],[f62])).
% 2.29/0.71  fof(f62,plain,(
% 2.29/0.71    spl4_2 <=> ! [X3,X2] : ~r1_xboole_0(X2,X3)),
% 2.29/0.71    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.29/0.71  fof(f41,plain,(
% 2.29/0.71    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.29/0.71    inference(cnf_transformation,[],[f13])).
% 2.29/0.71  fof(f13,plain,(
% 2.29/0.71    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.29/0.71    inference(rectify,[],[f3])).
% 2.29/0.71  fof(f3,axiom,(
% 2.29/0.71    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.29/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.29/0.71  fof(f67,plain,(
% 2.29/0.71    spl4_2 | spl4_3),
% 2.29/0.71    inference(avatar_split_clause,[],[f60,f65,f62])).
% 2.29/0.71  fof(f60,plain,(
% 2.29/0.71    ( ! [X4,X2,X3] : (~r2_hidden(X4,k1_xboole_0) | ~r1_xboole_0(X2,X3)) )),
% 2.29/0.71    inference(duplicate_literal_removal,[],[f59])).
% 2.29/0.71  fof(f59,plain,(
% 2.29/0.71    ( ! [X4,X2,X3] : (~r2_hidden(X4,k1_xboole_0) | ~r1_xboole_0(X2,X3) | ~r1_xboole_0(X2,X3)) )),
% 2.29/0.71    inference(superposition,[],[f45,f37])).
% 2.29/0.71  fof(f37,plain,(
% 2.29/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.29/0.71    inference(cnf_transformation,[],[f26])).
% 2.29/0.71  fof(f45,plain,(
% 2.29/0.71    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.29/0.71    inference(cnf_transformation,[],[f28])).
% 2.29/0.71  fof(f28,plain,(
% 2.29/0.71    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.29/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f27])).
% 2.29/0.71  fof(f27,plain,(
% 2.29/0.71    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 2.29/0.71    introduced(choice_axiom,[])).
% 2.29/0.71  fof(f18,plain,(
% 2.29/0.71    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.29/0.71    inference(ennf_transformation,[],[f14])).
% 2.29/0.71  fof(f14,plain,(
% 2.29/0.71    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.29/0.71    inference(rectify,[],[f4])).
% 2.29/0.71  fof(f4,axiom,(
% 2.29/0.71    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.29/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.29/0.71  fof(f53,plain,(
% 2.29/0.71    ~spl4_1),
% 2.29/0.71    inference(avatar_split_clause,[],[f29,f50])).
% 2.29/0.71  fof(f29,plain,(
% 2.29/0.71    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 2.29/0.71    inference(cnf_transformation,[],[f20])).
% 2.29/0.71  fof(f20,plain,(
% 2.29/0.71    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 2.29/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f19])).
% 2.29/0.71  fof(f19,plain,(
% 2.29/0.71    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 2.29/0.71    introduced(choice_axiom,[])).
% 2.29/0.71  fof(f15,plain,(
% 2.29/0.71    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 2.29/0.71    inference(ennf_transformation,[],[f12])).
% 2.29/0.71  fof(f12,negated_conjecture,(
% 2.29/0.71    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.29/0.71    inference(negated_conjecture,[],[f11])).
% 2.29/0.71  fof(f11,conjecture,(
% 2.29/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.29/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.29/0.71  % SZS output end Proof for theBenchmark
% 2.29/0.71  % (30948)------------------------------
% 2.29/0.71  % (30948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.71  % (30948)Termination reason: Refutation
% 2.29/0.71  
% 2.29/0.71  % (30948)Memory used [KB]: 7675
% 2.29/0.71  % (30948)Time elapsed: 0.304 s
% 2.29/0.71  % (30948)------------------------------
% 2.29/0.71  % (30948)------------------------------
% 2.29/0.71  % (30926)Success in time 0.34 s
%------------------------------------------------------------------------------

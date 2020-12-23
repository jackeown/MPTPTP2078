%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 215 expanded)
%              Number of leaves         :   15 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  207 ( 761 expanded)
%              Number of equality atoms :  159 ( 690 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f72,f78,f94,f118,f120,f150,f151])).

fof(f151,plain,
    ( spl12_2
    | ~ spl12_8 ),
    inference(avatar_split_clause,[],[f148,f115,f43])).

fof(f43,plain,
    ( spl12_2
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f115,plain,
    ( spl12_8
  <=> k4_tarski(sK4,sK5) = k4_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f148,plain,
    ( sK1 = sK5
    | ~ spl12_8 ),
    inference(forward_demodulation,[],[f143,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(X4,X5) != k4_tarski(X6,X7)
      | k2_mcart_1(k4_tarski(X4,X5)) = X5 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X5
      | k2_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X5
      | k4_tarski(X4,X5) != X0
      | k2_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ( sK9(X0,X1) != X1
              & k4_tarski(sK8(X0,X1),sK9(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f14,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X3
          & k4_tarski(X2,X3) = X0 )
     => ( sK9(X0,X1) != X1
        & k4_tarski(sK8(X0,X1),sK9(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X3
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k2_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X5
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X5
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X5 ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k2_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_mcart_1)).

fof(f143,plain,
    ( sK5 = k2_mcart_1(k4_tarski(sK0,sK1))
    | ~ spl12_8 ),
    inference(superposition,[],[f65,f117])).

fof(f117,plain,
    ( k4_tarski(sK4,sK5) = k4_tarski(sK0,sK1)
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f150,plain,
    ( spl12_1
    | ~ spl12_8 ),
    inference(avatar_split_clause,[],[f145,f115,f39])).

fof(f39,plain,
    ( spl12_1
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f145,plain,
    ( sK0 = sK4
    | ~ spl12_8 ),
    inference(forward_demodulation,[],[f141,f83])).

fof(f83,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(X4,X5) != k4_tarski(X6,X7)
      | k1_mcart_1(k4_tarski(X4,X5)) = X4 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X4
      | k1_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X4
      | k4_tarski(X4,X5) != X0
      | k1_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ( sK10(X0,X1) != X1
              & k4_tarski(sK10(X0,X1),sK11(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X2
          & k4_tarski(X2,X3) = X0 )
     => ( sK10(X0,X1) != X1
        & k4_tarski(sK10(X0,X1),sK11(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X2
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k1_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X4
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_mcart_1)).

fof(f141,plain,
    ( sK4 = k1_mcart_1(k4_tarski(sK0,sK1))
    | ~ spl12_8 ),
    inference(superposition,[],[f83,f117])).

fof(f120,plain,
    ( spl12_3
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f119,f91,f47])).

fof(f47,plain,
    ( spl12_3
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f91,plain,
    ( spl12_7
  <=> k4_tarski(k4_tarski(sK4,sK5),sK6) = k4_tarski(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f119,plain,
    ( sK2 = sK6
    | ~ spl12_7 ),
    inference(forward_demodulation,[],[f110,f65])).

% (21320)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f110,plain,
    ( sK6 = k2_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))
    | ~ spl12_7 ),
    inference(superposition,[],[f65,f93])).

fof(f93,plain,
    ( k4_tarski(k4_tarski(sK4,sK5),sK6) = k4_tarski(k4_tarski(sK0,sK1),sK2)
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f118,plain,
    ( spl12_8
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f113,f91,f115])).

fof(f113,plain,
    ( k4_tarski(sK4,sK5) = k4_tarski(sK0,sK1)
    | ~ spl12_7 ),
    inference(forward_demodulation,[],[f108,f83])).

fof(f108,plain,
    ( k4_tarski(sK4,sK5) = k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))
    | ~ spl12_7 ),
    inference(superposition,[],[f83,f93])).

fof(f94,plain,
    ( spl12_7
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f89,f75,f91])).

fof(f75,plain,
    ( spl12_6
  <=> k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f89,plain,
    ( k4_tarski(k4_tarski(sK4,sK5),sK6) = k4_tarski(k4_tarski(sK0,sK1),sK2)
    | ~ spl12_6 ),
    inference(forward_demodulation,[],[f88,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k1_mcart_1(k4_mcart_1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f83,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f88,plain,
    ( k4_tarski(k4_tarski(sK4,sK5),sK6) = k1_mcart_1(k4_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl12_6 ),
    inference(superposition,[],[f85,f77])).

fof(f77,plain,
    ( k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK3)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f78,plain,
    ( spl12_6
    | ~ spl12_4
    | ~ spl12_5 ),
    inference(avatar_split_clause,[],[f73,f56,f51,f75])).

fof(f51,plain,
    ( spl12_4
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f56,plain,
    ( spl12_5
  <=> k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f73,plain,
    ( k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK3)
    | ~ spl12_4
    | ~ spl12_5 ),
    inference(backward_demodulation,[],[f58,f52])).

fof(f52,plain,
    ( sK3 = sK7
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f58,plain,
    ( k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f72,plain,
    ( spl12_4
    | ~ spl12_5 ),
    inference(avatar_split_clause,[],[f71,f56,f51])).

fof(f71,plain,
    ( sK3 = sK7
    | ~ spl12_5 ),
    inference(forward_demodulation,[],[f70,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_mcart_1(k4_mcart_1(X0,X1,X2,X3)) = X3 ),
    inference(superposition,[],[f65,f23])).

fof(f70,plain,
    ( sK7 = k2_mcart_1(k4_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl12_5 ),
    inference(superposition,[],[f68,f58])).

fof(f59,plain,(
    spl12_5 ),
    inference(avatar_split_clause,[],[f21,f56])).

fof(f21,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
       => ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).

fof(f54,plain,
    ( ~ spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f22,f51,f47,f43,f39])).

fof(f22,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (21302)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (21299)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (21306)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.51  % (21308)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (21316)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (21298)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (21313)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.51  % (21308)Refutation not found, incomplete strategy% (21308)------------------------------
% 0.20/0.51  % (21308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21308)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (21308)Memory used [KB]: 1663
% 0.20/0.51  % (21308)Time elapsed: 0.074 s
% 0.20/0.51  % (21308)------------------------------
% 0.20/0.51  % (21308)------------------------------
% 0.20/0.51  % (21300)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (21296)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (21315)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (21297)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (21294)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (21315)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f54,f59,f72,f78,f94,f118,f120,f150,f151])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    spl12_2 | ~spl12_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f148,f115,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    spl12_2 <=> sK1 = sK5),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    spl12_8 <=> k4_tarski(sK4,sK5) = k4_tarski(sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    sK1 = sK5 | ~spl12_8),
% 0.20/0.52    inference(forward_demodulation,[],[f143,f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.20/0.52    inference(equality_resolution,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X6,X4,X7,X5] : (k4_tarski(X4,X5) != k4_tarski(X6,X7) | k2_mcart_1(k4_tarski(X4,X5)) = X5) )),
% 0.20/0.52    inference(equality_resolution,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X6,X4,X7,X5,X1] : (X1 = X5 | k2_mcart_1(k4_tarski(X4,X5)) != X1 | k4_tarski(X4,X5) != k4_tarski(X6,X7)) )),
% 0.20/0.52    inference(equality_resolution,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X6,X4,X0,X7,X5,X1] : (X1 = X5 | k4_tarski(X4,X5) != X0 | k2_mcart_1(X0) != X1 | k4_tarski(X6,X7) != X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((k2_mcart_1(X0) = X1 | (sK9(X0,X1) != X1 & k4_tarski(sK8(X0,X1),sK9(X0,X1)) = X0)) & (! [X4,X5] : (X1 = X5 | k4_tarski(X4,X5) != X0) | k2_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f14,f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2,X3] : (X1 != X3 & k4_tarski(X2,X3) = X0) => (sK9(X0,X1) != X1 & k4_tarski(sK8(X0,X1),sK9(X0,X1)) = X0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((k2_mcart_1(X0) = X1 | ? [X2,X3] : (X1 != X3 & k4_tarski(X2,X3) = X0)) & (! [X4,X5] : (X1 = X5 | k4_tarski(X4,X5) != X0) | k2_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 0.20/0.52    inference(rectify,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : (! [X3] : ((k2_mcart_1(X0) = X3 | ? [X4,X5] : (X3 != X5 & k4_tarski(X4,X5) = X0)) & (! [X4,X5] : (X3 = X5 | k4_tarski(X4,X5) != X0) | k2_mcart_1(X0) != X3)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.20/0.52    inference(nnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ! [X0] : (! [X3] : (k2_mcart_1(X0) = X3 <=> ! [X4,X5] : (X3 = X5 | k4_tarski(X4,X5) != X0)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,plain,(
% 0.20/0.52    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X3] : (k2_mcart_1(X0) = X3 <=> ! [X4,X5] : (k4_tarski(X4,X5) = X0 => X3 = X5)))),
% 0.20/0.52    inference(rectify,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X1] : (k2_mcart_1(X0) = X1 <=> ! [X2,X3] : (k4_tarski(X2,X3) = X0 => X1 = X3)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_mcart_1)).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    sK5 = k2_mcart_1(k4_tarski(sK0,sK1)) | ~spl12_8),
% 0.20/0.52    inference(superposition,[],[f65,f117])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    k4_tarski(sK4,sK5) = k4_tarski(sK0,sK1) | ~spl12_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f115])).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    spl12_1 | ~spl12_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f145,f115,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    spl12_1 <=> sK0 = sK4),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    sK0 = sK4 | ~spl12_8),
% 0.20/0.52    inference(forward_demodulation,[],[f141,f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.20/0.52    inference(equality_resolution,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X6,X4,X7,X5] : (k4_tarski(X4,X5) != k4_tarski(X6,X7) | k1_mcart_1(k4_tarski(X4,X5)) = X4) )),
% 0.20/0.52    inference(equality_resolution,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X6,X4,X7,X5,X1] : (X1 = X4 | k1_mcart_1(k4_tarski(X4,X5)) != X1 | k4_tarski(X4,X5) != k4_tarski(X6,X7)) )),
% 0.20/0.52    inference(equality_resolution,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X6,X4,X0,X7,X5,X1] : (X1 = X4 | k4_tarski(X4,X5) != X0 | k1_mcart_1(X0) != X1 | k4_tarski(X6,X7) != X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((k1_mcart_1(X0) = X1 | (sK10(X0,X1) != X1 & k4_tarski(sK10(X0,X1),sK11(X0,X1)) = X0)) & (! [X4,X5] : (X1 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f18,f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2,X3] : (X1 != X2 & k4_tarski(X2,X3) = X0) => (sK10(X0,X1) != X1 & k4_tarski(sK10(X0,X1),sK11(X0,X1)) = X0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((k1_mcart_1(X0) = X1 | ? [X2,X3] : (X1 != X2 & k4_tarski(X2,X3) = X0)) & (! [X4,X5] : (X1 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 0.20/0.52    inference(rectify,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (! [X3] : ((k1_mcart_1(X0) = X3 | ? [X4,X5] : (X3 != X4 & k4_tarski(X4,X5) = X0)) & (! [X4,X5] : (X3 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X3)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.20/0.52    inference(nnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ! [X0] : (! [X3] : (k1_mcart_1(X0) = X3 <=> ! [X4,X5] : (X3 = X4 | k4_tarski(X4,X5) != X0)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,plain,(
% 0.20/0.52    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X3] : (k1_mcart_1(X0) = X3 <=> ! [X4,X5] : (k4_tarski(X4,X5) = X0 => X3 = X4)))),
% 0.20/0.52    inference(rectify,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X1] : (k1_mcart_1(X0) = X1 <=> ! [X2,X3] : (k4_tarski(X2,X3) = X0 => X1 = X2)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_mcart_1)).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    sK4 = k1_mcart_1(k4_tarski(sK0,sK1)) | ~spl12_8),
% 0.20/0.52    inference(superposition,[],[f83,f117])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    spl12_3 | ~spl12_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f119,f91,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    spl12_3 <=> sK2 = sK6),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    spl12_7 <=> k4_tarski(k4_tarski(sK4,sK5),sK6) = k4_tarski(k4_tarski(sK0,sK1),sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    sK2 = sK6 | ~spl12_7),
% 0.20/0.52    inference(forward_demodulation,[],[f110,f65])).
% 0.20/0.52  % (21320)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    sK6 = k2_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) | ~spl12_7),
% 0.20/0.52    inference(superposition,[],[f65,f93])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    k4_tarski(k4_tarski(sK4,sK5),sK6) = k4_tarski(k4_tarski(sK0,sK1),sK2) | ~spl12_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f91])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    spl12_8 | ~spl12_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f113,f91,f115])).
% 0.20/0.52  fof(f113,plain,(
% 0.20/0.52    k4_tarski(sK4,sK5) = k4_tarski(sK0,sK1) | ~spl12_7),
% 0.20/0.52    inference(forward_demodulation,[],[f108,f83])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    k4_tarski(sK4,sK5) = k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) | ~spl12_7),
% 0.20/0.52    inference(superposition,[],[f83,f93])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    spl12_7 | ~spl12_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f89,f75,f91])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    spl12_6 <=> k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    k4_tarski(k4_tarski(sK4,sK5),sK6) = k4_tarski(k4_tarski(sK0,sK1),sK2) | ~spl12_6),
% 0.20/0.52    inference(forward_demodulation,[],[f88,f85])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k1_mcart_1(k4_mcart_1(X0,X1,X2,X3))) )),
% 0.20/0.52    inference(superposition,[],[f83,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    k4_tarski(k4_tarski(sK4,sK5),sK6) = k1_mcart_1(k4_mcart_1(sK0,sK1,sK2,sK3)) | ~spl12_6),
% 0.20/0.52    inference(superposition,[],[f85,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK3) | ~spl12_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f75])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    spl12_6 | ~spl12_4 | ~spl12_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f73,f56,f51,f75])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    spl12_4 <=> sK3 = sK7),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    spl12_5 <=> k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK3) | (~spl12_4 | ~spl12_5)),
% 0.20/0.52    inference(backward_demodulation,[],[f58,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    sK3 = sK7 | ~spl12_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f51])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) | ~spl12_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f56])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    spl12_4 | ~spl12_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f71,f56,f51])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    sK3 = sK7 | ~spl12_5),
% 0.20/0.52    inference(forward_demodulation,[],[f70,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k4_mcart_1(X0,X1,X2,X3)) = X3) )),
% 0.20/0.52    inference(superposition,[],[f65,f23])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    sK7 = k2_mcart_1(k4_mcart_1(sK0,sK1,sK2,sK3)) | ~spl12_5),
% 0.20/0.52    inference(superposition,[],[f68,f58])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    spl12_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f21,f56])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.20/0.52    inference(negated_conjecture,[],[f4])).
% 0.20/0.52  fof(f4,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ~spl12_1 | ~spl12_2 | ~spl12_3 | ~spl12_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f22,f51,f47,f43,f39])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (21315)------------------------------
% 0.20/0.52  % (21315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (21315)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (21315)Memory used [KB]: 6268
% 0.20/0.52  % (21315)Time elapsed: 0.128 s
% 0.20/0.52  % (21315)------------------------------
% 0.20/0.52  % (21315)------------------------------
% 0.20/0.52  % (21293)Success in time 0.161 s
%------------------------------------------------------------------------------

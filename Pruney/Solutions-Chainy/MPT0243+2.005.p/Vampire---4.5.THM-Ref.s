%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:40 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 117 expanded)
%              Number of leaves         :   13 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  266 ( 515 expanded)
%              Number of equality atoms :   87 ( 169 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f106,f107,f164,f202,f203])).

fof(f203,plain,
    ( spl6_3
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f179,f94,f102])).

fof(f102,plain,
    ( spl6_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f94,plain,
    ( spl6_1
  <=> r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f179,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f87,f95,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f95,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f87,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK5(X0,X1,X2,X3) != X2
              & sK5(X0,X1,X2,X3) != X1
              & sK5(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sK5(X0,X1,X2,X3) = X2
            | sK5(X0,X1,X2,X3) = X1
            | sK5(X0,X1,X2,X3) = X0
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK5(X0,X1,X2,X3) != X2
            & sK5(X0,X1,X2,X3) != X1
            & sK5(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sK5(X0,X1,X2,X3) = X2
          | sK5(X0,X1,X2,X3) = X1
          | sK5(X0,X1,X2,X3) = X0
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f202,plain,
    ( spl6_2
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f182,f94,f98])).

fof(f98,plain,
    ( spl6_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f182,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f91,f95,f55])).

fof(f91,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f164,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f162,f96])).

fof(f96,plain,
    ( ~ r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f162,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f157,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_enumset1(X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f157,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f116,f127,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f127,plain,
    ( r1_tarski(k1_tarski(sK1),sK2)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f103,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f103,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f116,plain,
    ( r1_tarski(k1_tarski(sK0),sK2)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f99,f59])).

fof(f99,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f107,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f78,f98,f94])).

fof(f78,plain,
    ( r2_hidden(sK0,sK2)
    | r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f44,plain,
    ( r2_hidden(sK0,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | r1_tarski(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | ~ r1_tarski(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | r1_tarski(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | r1_tarski(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f106,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f77,f102,f94])).

fof(f77,plain,
    ( r2_hidden(sK1,sK2)
    | r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f45,plain,
    ( r2_hidden(sK1,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f105,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f76,f102,f98,f94])).

fof(f76,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f46,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:53:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (22559)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (22583)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (22575)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (22581)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (22563)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (22572)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (22580)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.28/0.53  % (22564)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.28/0.53  % (22557)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.53  % (22558)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.53  % (22562)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.53  % (22561)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.28/0.53  % (22579)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.53  % (22583)Refutation found. Thanks to Tanya!
% 1.28/0.53  % SZS status Theorem for theBenchmark
% 1.28/0.53  % (22579)Refutation not found, incomplete strategy% (22579)------------------------------
% 1.28/0.53  % (22579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (22579)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (22579)Memory used [KB]: 10746
% 1.28/0.53  % (22579)Time elapsed: 0.120 s
% 1.28/0.53  % (22579)------------------------------
% 1.28/0.53  % (22579)------------------------------
% 1.28/0.53  % SZS output start Proof for theBenchmark
% 1.28/0.53  fof(f206,plain,(
% 1.28/0.53    $false),
% 1.28/0.53    inference(avatar_sat_refutation,[],[f105,f106,f107,f164,f202,f203])).
% 1.28/0.53  fof(f203,plain,(
% 1.28/0.53    spl6_3 | ~spl6_1),
% 1.28/0.53    inference(avatar_split_clause,[],[f179,f94,f102])).
% 1.28/0.53  fof(f102,plain,(
% 1.28/0.53    spl6_3 <=> r2_hidden(sK1,sK2)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.28/0.53  fof(f94,plain,(
% 1.28/0.53    spl6_1 <=> r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.28/0.53  fof(f179,plain,(
% 1.28/0.53    r2_hidden(sK1,sK2) | ~spl6_1),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f87,f95,f55])).
% 1.28/0.53  fof(f55,plain,(
% 1.28/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f32])).
% 1.28/0.53  fof(f32,plain,(
% 1.28/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 1.28/0.53  fof(f31,plain,(
% 1.28/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f30,plain,(
% 1.28/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.28/0.53    inference(rectify,[],[f29])).
% 1.28/0.53  fof(f29,plain,(
% 1.28/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.28/0.53    inference(nnf_transformation,[],[f18])).
% 1.28/0.53  fof(f18,plain,(
% 1.28/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.28/0.53    inference(ennf_transformation,[],[f1])).
% 1.28/0.53  fof(f1,axiom,(
% 1.28/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.28/0.53  fof(f95,plain,(
% 1.28/0.53    r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) | ~spl6_1),
% 1.28/0.53    inference(avatar_component_clause,[],[f94])).
% 1.28/0.53  fof(f87,plain,(
% 1.28/0.53    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 1.28/0.53    inference(equality_resolution,[],[f86])).
% 1.28/0.53  fof(f86,plain,(
% 1.28/0.53    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 1.28/0.53    inference(equality_resolution,[],[f71])).
% 1.28/0.53  fof(f71,plain,(
% 1.28/0.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.28/0.53    inference(cnf_transformation,[],[f43])).
% 1.28/0.53  fof(f43,plain,(
% 1.28/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 1.28/0.54  fof(f42,plain,(
% 1.28/0.54    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  fof(f41,plain,(
% 1.28/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.28/0.54    inference(rectify,[],[f40])).
% 1.28/0.54  fof(f40,plain,(
% 1.28/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.28/0.54    inference(flattening,[],[f39])).
% 1.28/0.54  fof(f39,plain,(
% 1.28/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.28/0.54    inference(nnf_transformation,[],[f22])).
% 1.28/0.54  fof(f22,plain,(
% 1.28/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.28/0.54    inference(ennf_transformation,[],[f8])).
% 1.28/0.54  fof(f8,axiom,(
% 1.28/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.28/0.54  fof(f202,plain,(
% 1.28/0.54    spl6_2 | ~spl6_1),
% 1.28/0.54    inference(avatar_split_clause,[],[f182,f94,f98])).
% 1.28/0.54  fof(f98,plain,(
% 1.28/0.54    spl6_2 <=> r2_hidden(sK0,sK2)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.28/0.54  fof(f182,plain,(
% 1.28/0.54    r2_hidden(sK0,sK2) | ~spl6_1),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f91,f95,f55])).
% 1.28/0.54  fof(f91,plain,(
% 1.28/0.54    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 1.28/0.54    inference(equality_resolution,[],[f90])).
% 1.28/0.54  fof(f90,plain,(
% 1.28/0.54    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 1.28/0.54    inference(equality_resolution,[],[f69])).
% 1.28/0.54  fof(f69,plain,(
% 1.28/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.28/0.54    inference(cnf_transformation,[],[f43])).
% 1.28/0.54  fof(f164,plain,(
% 1.28/0.54    spl6_1 | ~spl6_2 | ~spl6_3),
% 1.28/0.54    inference(avatar_contradiction_clause,[],[f163])).
% 1.28/0.54  fof(f163,plain,(
% 1.28/0.54    $false | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.28/0.54    inference(subsumption_resolution,[],[f162,f96])).
% 1.28/0.54  fof(f96,plain,(
% 1.28/0.54    ~r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) | spl6_1),
% 1.28/0.54    inference(avatar_component_clause,[],[f94])).
% 1.28/0.54  fof(f162,plain,(
% 1.28/0.54    r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) | (~spl6_2 | ~spl6_3)),
% 1.28/0.54    inference(forward_demodulation,[],[f157,f80])).
% 1.28/0.54  fof(f80,plain,(
% 1.28/0.54    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_enumset1(X0,X0,X1)) )),
% 1.28/0.54    inference(definition_unfolding,[],[f49,f48])).
% 1.28/0.54  fof(f48,plain,(
% 1.28/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f10])).
% 1.28/0.54  fof(f10,axiom,(
% 1.28/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.28/0.54  fof(f49,plain,(
% 1.28/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.28/0.54    inference(cnf_transformation,[],[f9])).
% 1.28/0.54  fof(f9,axiom,(
% 1.28/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 1.28/0.54  fof(f157,plain,(
% 1.28/0.54    r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) | (~spl6_2 | ~spl6_3)),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f116,f127,f61])).
% 1.28/0.54  fof(f61,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f21])).
% 1.28/0.54  fof(f21,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.28/0.54    inference(flattening,[],[f20])).
% 1.28/0.54  fof(f20,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.28/0.54    inference(ennf_transformation,[],[f7])).
% 1.28/0.54  fof(f7,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.28/0.54  fof(f127,plain,(
% 1.28/0.54    r1_tarski(k1_tarski(sK1),sK2) | ~spl6_3),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f103,f59])).
% 1.28/0.54  fof(f59,plain,(
% 1.28/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f33])).
% 1.28/0.54  fof(f33,plain,(
% 1.28/0.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.28/0.54    inference(nnf_transformation,[],[f11])).
% 1.28/0.54  fof(f11,axiom,(
% 1.28/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.28/0.54  fof(f103,plain,(
% 1.28/0.54    r2_hidden(sK1,sK2) | ~spl6_3),
% 1.28/0.54    inference(avatar_component_clause,[],[f102])).
% 1.28/0.54  fof(f116,plain,(
% 1.28/0.54    r1_tarski(k1_tarski(sK0),sK2) | ~spl6_2),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f99,f59])).
% 1.28/0.54  fof(f99,plain,(
% 1.28/0.54    r2_hidden(sK0,sK2) | ~spl6_2),
% 1.28/0.54    inference(avatar_component_clause,[],[f98])).
% 1.28/0.54  fof(f107,plain,(
% 1.28/0.54    spl6_1 | spl6_2),
% 1.28/0.54    inference(avatar_split_clause,[],[f78,f98,f94])).
% 1.28/0.54  fof(f78,plain,(
% 1.28/0.54    r2_hidden(sK0,sK2) | r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)),
% 1.28/0.54    inference(definition_unfolding,[],[f44,f48])).
% 1.28/0.54  fof(f44,plain,(
% 1.28/0.54    r2_hidden(sK0,sK2) | r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 1.28/0.54    inference(cnf_transformation,[],[f26])).
% 1.28/0.54  fof(f26,plain,(
% 1.28/0.54    (~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | r1_tarski(k2_tarski(sK0,sK1),sK2))),
% 1.28/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f25])).
% 1.28/0.54  fof(f25,plain,(
% 1.28/0.54    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | r1_tarski(k2_tarski(sK0,sK1),sK2)))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  fof(f24,plain,(
% 1.28/0.54    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.28/0.54    inference(flattening,[],[f23])).
% 1.28/0.54  fof(f23,plain,(
% 1.28/0.54    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.28/0.54    inference(nnf_transformation,[],[f15])).
% 1.28/0.54  fof(f15,plain,(
% 1.28/0.54    ? [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.28/0.54    inference(ennf_transformation,[],[f14])).
% 1.28/0.54  fof(f14,negated_conjecture,(
% 1.28/0.54    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.28/0.54    inference(negated_conjecture,[],[f13])).
% 1.28/0.54  fof(f13,conjecture,(
% 1.28/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.28/0.54  fof(f106,plain,(
% 1.28/0.54    spl6_1 | spl6_3),
% 1.28/0.54    inference(avatar_split_clause,[],[f77,f102,f94])).
% 1.28/0.54  fof(f77,plain,(
% 1.28/0.54    r2_hidden(sK1,sK2) | r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)),
% 1.28/0.54    inference(definition_unfolding,[],[f45,f48])).
% 1.28/0.54  fof(f45,plain,(
% 1.28/0.54    r2_hidden(sK1,sK2) | r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 1.28/0.54    inference(cnf_transformation,[],[f26])).
% 1.28/0.54  fof(f105,plain,(
% 1.28/0.54    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 1.28/0.54    inference(avatar_split_clause,[],[f76,f102,f98,f94])).
% 1.28/0.54  fof(f76,plain,(
% 1.28/0.54    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)),
% 1.28/0.54    inference(definition_unfolding,[],[f46,f48])).
% 1.28/0.54  fof(f46,plain,(
% 1.28/0.54    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 1.28/0.54    inference(cnf_transformation,[],[f26])).
% 1.28/0.54  % SZS output end Proof for theBenchmark
% 1.28/0.54  % (22583)------------------------------
% 1.28/0.54  % (22583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (22583)Termination reason: Refutation
% 1.28/0.54  
% 1.28/0.54  % (22560)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.54  % (22583)Memory used [KB]: 10746
% 1.28/0.54  % (22583)Time elapsed: 0.119 s
% 1.28/0.54  % (22583)------------------------------
% 1.28/0.54  % (22583)------------------------------
% 1.28/0.54  % (22556)Success in time 0.176 s
%------------------------------------------------------------------------------

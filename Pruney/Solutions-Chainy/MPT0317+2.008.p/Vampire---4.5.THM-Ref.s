%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 111 expanded)
%              Number of leaves         :   12 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  230 ( 454 expanded)
%              Number of equality atoms :   83 ( 174 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f57,f61,f68,f77,f81,f85,f86])).

fof(f86,plain,
    ( sK1 != sK3
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK1,sK1)))
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f85,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl5_1
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f42,f51,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

% (14198)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f51,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f50])).

% (14197)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f50,plain,
    ( spl5_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f42,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl5_1
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f81,plain,
    ( spl5_2
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl5_2
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f45,f45,f76,f38])).

fof(f38,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

% (14203)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f76,plain,
    ( r2_hidden(sK1,k2_tarski(sK3,sK3))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_5
  <=> r2_hidden(sK1,k2_tarski(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f45,plain,
    ( sK1 != sK3
    | spl5_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl5_2
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f77,plain,
    ( spl5_5
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f69,f40,f74])).

fof(f69,plain,
    ( r2_hidden(sK1,k2_tarski(sK3,sK3))
    | ~ spl5_1 ),
    inference(resolution,[],[f42,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | ~ spl5_3
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f52,f35,f55,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK1,sK1)))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_4
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f35,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f61,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f60,f44,f54,f50])).

fof(f60,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK1,sK1)))
    | ~ r2_hidden(sK0,sK2)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f59,f46])).

fof(f46,plain,
    ( sK1 = sK3
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f59,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))
    | ~ spl5_2 ),
    inference(trivial_inequality_removal,[],[f58])).

fof(f58,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f31,f46])).

fof(f31,plain,
    ( sK1 != sK3
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) ),
    inference(definition_unfolding,[],[f20,f27])).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,
    ( sK1 != sK3
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( sK1 != sK3
      | ~ r2_hidden(sK0,sK2)
      | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) )
    & ( ( sK1 = sK3
        & r2_hidden(sK0,sK2) )
      | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | ~ r2_hidden(X0,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
        & ( ( X1 = X3
            & r2_hidden(X0,X2) )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) )
   => ( ( sK1 != sK3
        | ~ r2_hidden(sK0,sK2)
        | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) )
      & ( ( sK1 = sK3
          & r2_hidden(sK0,sK2) )
        | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ) ) ),
    introduced(choice_axiom,[])).

% (14211)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (14219)Refutation not found, incomplete strategy% (14219)------------------------------
% (14219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14219)Termination reason: Refutation not found, incomplete strategy

% (14219)Memory used [KB]: 10618
% (14219)Time elapsed: 0.153 s
% (14219)------------------------------
% (14219)------------------------------
fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <~> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      <=> ( X1 = X3
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f57,plain,
    ( spl5_3
    | spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f48,f44,f54,f50])).

fof(f48,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK1,sK1)))
    | r2_hidden(sK0,sK2)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f33,f46])).

% (14208)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f33,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) ),
    inference(definition_unfolding,[],[f18,f27])).

fof(f18,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f32,f44,f40])).

fof(f32,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) ),
    inference(definition_unfolding,[],[f19,f27])).

fof(f19,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:00:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (14201)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (14207)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (14206)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (14218)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (14218)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (14199)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.56  % (14196)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.56  % (14219)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (14210)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (14217)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f47,f57,f61,f68,f77,f81,f85,f86])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    sK1 != sK3 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK1,sK1))) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))),
% 0.21/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    ~spl5_1 | spl5_3),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f84])).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    $false | (~spl5_1 | spl5_3)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f42,f51,f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.56    inference(flattening,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.57    inference(nnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.57  % (14198)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ~r2_hidden(sK0,sK2) | spl5_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f50])).
% 0.21/0.57  % (14197)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    spl5_3 <=> r2_hidden(sK0,sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) | ~spl5_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    spl5_1 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    spl5_2 | ~spl5_5),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f78])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    $false | (spl5_2 | ~spl5_5)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f45,f45,f76,f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.21/0.57    inference(equality_resolution,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.57    inference(rectify,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.57    inference(flattening,[],[f11])).
% 0.21/0.57  % (14203)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.57    inference(nnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    r2_hidden(sK1,k2_tarski(sK3,sK3)) | ~spl5_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f74])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    spl5_5 <=> r2_hidden(sK1,k2_tarski(sK3,sK3))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    sK1 != sK3 | spl5_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    spl5_2 <=> sK1 = sK3),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    spl5_5 | ~spl5_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f69,f40,f74])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    r2_hidden(sK1,k2_tarski(sK3,sK3)) | ~spl5_1),
% 0.21/0.57    inference(resolution,[],[f42,f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    ~spl5_3 | spl5_4),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f64])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    $false | (~spl5_3 | spl5_4)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f52,f35,f55,f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK1,sK1))) | spl5_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    spl5_4 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK1,sK1)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 0.21/0.57    inference(equality_resolution,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 0.21/0.57    inference(equality_resolution,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    r2_hidden(sK0,sK2) | ~spl5_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f50])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ~spl5_3 | ~spl5_4 | ~spl5_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f60,f44,f54,f50])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK1,sK1))) | ~r2_hidden(sK0,sK2) | ~spl5_2),
% 0.21/0.57    inference(forward_demodulation,[],[f59,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    sK1 = sK3 | ~spl5_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f44])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) | ~spl5_2),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f58])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    sK1 != sK1 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) | ~spl5_2),
% 0.21/0.57    inference(forward_demodulation,[],[f31,f46])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    sK1 != sK3 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))),
% 0.21/0.57    inference(definition_unfolding,[],[f20,f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    sK1 != sK3 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,plain,(
% 0.21/0.57    (sK1 != sK3 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))) & ((sK1 = sK3 & r2_hidden(sK0,sK2)) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).
% 0.21/0.57  fof(f9,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : ((X1 != X3 | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))))) => ((sK1 != sK3 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))) & ((sK1 = sK3 & r2_hidden(sK0,sK2)) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  % (14211)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.57  % (14219)Refutation not found, incomplete strategy% (14219)------------------------------
% 0.21/0.57  % (14219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (14219)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (14219)Memory used [KB]: 10618
% 0.21/0.57  % (14219)Time elapsed: 0.153 s
% 0.21/0.57  % (14219)------------------------------
% 0.21/0.57  % (14219)------------------------------
% 0.21/0.57  fof(f8,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : ((X1 != X3 | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.21/0.57    inference(flattening,[],[f7])).
% 0.21/0.57  fof(f7,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : (((X1 != X3 | ~r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.21/0.57    inference(nnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <~> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.21/0.57    inference(negated_conjecture,[],[f4])).
% 0.21/0.57  fof(f4,conjecture,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    spl5_3 | spl5_4 | ~spl5_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f48,f44,f54,f50])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK1,sK1))) | r2_hidden(sK0,sK2) | ~spl5_2),
% 0.21/0.57    inference(forward_demodulation,[],[f33,f46])).
% 0.21/0.57  % (14208)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    r2_hidden(sK0,sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))),
% 0.21/0.57    inference(definition_unfolding,[],[f18,f27])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    r2_hidden(sK0,sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    spl5_1 | spl5_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f32,f44,f40])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    sK1 = sK3 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))),
% 0.21/0.57    inference(definition_unfolding,[],[f19,f27])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    sK1 = sK3 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (14218)------------------------------
% 0.21/0.57  % (14218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (14218)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (14218)Memory used [KB]: 10746
% 0.21/0.57  % (14218)Time elapsed: 0.130 s
% 0.21/0.57  % (14218)------------------------------
% 0.21/0.57  % (14218)------------------------------
% 0.21/0.57  % (14202)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.57  % (14194)Success in time 0.215 s
%------------------------------------------------------------------------------

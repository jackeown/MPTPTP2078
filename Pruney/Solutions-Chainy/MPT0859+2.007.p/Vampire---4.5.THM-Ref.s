%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:20 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   46 (  76 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   15
%              Number of atoms          :  195 ( 290 expanded)
%              Number of equality atoms :  119 ( 164 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f65,f77])).

fof(f77,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f75,f52])).

fof(f52,plain,
    ( sK2 != k1_mcart_1(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl5_1
  <=> sK2 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f75,plain,
    ( sK2 = k1_mcart_1(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f74,f61])).

fof(f61,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_3
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f74,plain,
    ( sK1 = k1_mcart_1(sK0)
    | sK2 = k1_mcart_1(sK0) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,
    ( sK1 = k1_mcart_1(sK0)
    | sK2 = k1_mcart_1(sK0)
    | sK1 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f69,f33])).

fof(f33,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f17,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f17,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X3)
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
        | ( sK2 != k1_mcart_1(sK0)
          & sK1 != k1_mcart_1(sK0) ) )
      & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X3)
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
       => ( r2_hidden(k2_mcart_1(X0),X3)
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

fof(f69,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ r2_hidden(X10,k2_zfmisc_1(k2_enumset1(X11,X11,X9,X12),X13))
      | k1_mcart_1(X10) = X11
      | k1_mcart_1(X10) = X12
      | k1_mcart_1(X10) = X9 ) ),
    inference(resolution,[],[f48,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f48,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f24,f21])).

fof(f24,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f15])).

fof(f15,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f65,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | spl5_2 ),
    inference(resolution,[],[f63,f33])).

fof(f63,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k2_zfmisc_1(X0,sK3))
    | spl5_2 ),
    inference(resolution,[],[f23,f56])).

fof(f56,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_2
  <=> r2_hidden(k2_mcart_1(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f62,plain,
    ( ~ spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f18,f54,f59])).

fof(f18,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f19,f54,f50])).

fof(f19,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:19:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.37  ipcrm: permission denied for id (809500676)
% 0.20/0.37  ipcrm: permission denied for id (809533446)
% 0.20/0.38  ipcrm: permission denied for id (809566218)
% 0.20/0.38  ipcrm: permission denied for id (809631757)
% 0.20/0.38  ipcrm: permission denied for id (809664527)
% 0.20/0.39  ipcrm: permission denied for id (809697296)
% 0.20/0.39  ipcrm: permission denied for id (809762838)
% 0.20/0.39  ipcrm: permission denied for id (809795607)
% 0.20/0.40  ipcrm: permission denied for id (809828378)
% 0.20/0.40  ipcrm: permission denied for id (809861149)
% 0.20/0.40  ipcrm: permission denied for id (809893918)
% 0.20/0.41  ipcrm: permission denied for id (809926691)
% 0.20/0.42  ipcrm: permission denied for id (809959469)
% 0.20/0.43  ipcrm: permission denied for id (809992240)
% 0.20/0.43  ipcrm: permission denied for id (810025011)
% 0.20/0.43  ipcrm: permission denied for id (810057781)
% 0.20/0.45  ipcrm: permission denied for id (810156096)
% 0.20/0.45  ipcrm: permission denied for id (810221635)
% 0.20/0.46  ipcrm: permission denied for id (810254409)
% 0.20/0.46  ipcrm: permission denied for id (810319950)
% 0.20/0.47  ipcrm: permission denied for id (810352719)
% 0.20/0.47  ipcrm: permission denied for id (810385488)
% 0.20/0.48  ipcrm: permission denied for id (810451032)
% 0.20/0.48  ipcrm: permission denied for id (810483802)
% 0.20/0.49  ipcrm: permission denied for id (810582116)
% 0.20/0.50  ipcrm: permission denied for id (810647656)
% 0.20/0.51  ipcrm: permission denied for id (810745969)
% 0.20/0.52  ipcrm: permission denied for id (810844279)
% 0.20/0.52  ipcrm: permission denied for id (810909819)
% 0.20/0.52  ipcrm: permission denied for id (810942589)
% 0.38/0.67  % (23691)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.38/0.67  % (23685)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.38/0.68  % (23704)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.38/0.68  % (23685)Refutation found. Thanks to Tanya!
% 0.38/0.68  % SZS status Theorem for theBenchmark
% 0.38/0.68  % SZS output start Proof for theBenchmark
% 0.38/0.68  fof(f78,plain,(
% 0.38/0.68    $false),
% 0.38/0.68    inference(avatar_sat_refutation,[],[f57,f62,f65,f77])).
% 0.38/0.68  fof(f77,plain,(
% 0.38/0.68    spl5_1 | spl5_3),
% 0.38/0.68    inference(avatar_contradiction_clause,[],[f76])).
% 0.38/0.68  fof(f76,plain,(
% 0.38/0.68    $false | (spl5_1 | spl5_3)),
% 0.38/0.68    inference(subsumption_resolution,[],[f75,f52])).
% 0.38/0.68  fof(f52,plain,(
% 0.38/0.68    sK2 != k1_mcart_1(sK0) | spl5_1),
% 0.38/0.68    inference(avatar_component_clause,[],[f50])).
% 0.38/0.68  fof(f50,plain,(
% 0.38/0.68    spl5_1 <=> sK2 = k1_mcart_1(sK0)),
% 0.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.38/0.68  fof(f75,plain,(
% 0.38/0.68    sK2 = k1_mcart_1(sK0) | spl5_3),
% 0.38/0.68    inference(subsumption_resolution,[],[f74,f61])).
% 0.38/0.68  fof(f61,plain,(
% 0.38/0.68    sK1 != k1_mcart_1(sK0) | spl5_3),
% 0.38/0.68    inference(avatar_component_clause,[],[f59])).
% 0.38/0.68  fof(f59,plain,(
% 0.38/0.68    spl5_3 <=> sK1 = k1_mcart_1(sK0)),
% 0.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.38/0.68  fof(f74,plain,(
% 0.38/0.68    sK1 = k1_mcart_1(sK0) | sK2 = k1_mcart_1(sK0)),
% 0.38/0.68    inference(duplicate_literal_removal,[],[f73])).
% 0.38/0.68  fof(f73,plain,(
% 0.38/0.68    sK1 = k1_mcart_1(sK0) | sK2 = k1_mcart_1(sK0) | sK1 = k1_mcart_1(sK0)),
% 0.38/0.68    inference(resolution,[],[f69,f33])).
% 0.38/0.68  fof(f33,plain,(
% 0.38/0.68    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),sK3))),
% 0.38/0.68    inference(definition_unfolding,[],[f17,f32])).
% 0.38/0.68  fof(f32,plain,(
% 0.38/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.38/0.68    inference(definition_unfolding,[],[f20,f21])).
% 0.38/0.68  fof(f21,plain,(
% 0.38/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.38/0.68    inference(cnf_transformation,[],[f3])).
% 0.38/0.68  fof(f3,axiom,(
% 0.38/0.68    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.38/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.38/0.68  fof(f20,plain,(
% 0.38/0.68    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.38/0.68    inference(cnf_transformation,[],[f2])).
% 0.38/0.68  fof(f2,axiom,(
% 0.38/0.68    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.38/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.38/0.68  fof(f17,plain,(
% 0.38/0.68    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3))),
% 0.38/0.68    inference(cnf_transformation,[],[f11])).
% 0.38/0.68  fof(f11,plain,(
% 0.38/0.68    (~r2_hidden(k2_mcart_1(sK0),sK3) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3))),
% 0.38/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f10])).
% 0.38/0.68  fof(f10,plain,(
% 0.38/0.68    ? [X0,X1,X2,X3] : ((~r2_hidden(k2_mcart_1(X0),X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))) => ((~r2_hidden(k2_mcart_1(sK0),sK3) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)))),
% 0.38/0.68    introduced(choice_axiom,[])).
% 0.38/0.68  fof(f7,plain,(
% 0.38/0.68    ? [X0,X1,X2,X3] : ((~r2_hidden(k2_mcart_1(X0),X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)))),
% 0.38/0.68    inference(ennf_transformation,[],[f6])).
% 0.38/0.68  fof(f6,negated_conjecture,(
% 0.38/0.68    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.38/0.68    inference(negated_conjecture,[],[f5])).
% 0.38/0.68  fof(f5,conjecture,(
% 0.38/0.68    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.38/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).
% 0.38/0.68  fof(f69,plain,(
% 0.38/0.68    ( ! [X12,X10,X13,X11,X9] : (~r2_hidden(X10,k2_zfmisc_1(k2_enumset1(X11,X11,X9,X12),X13)) | k1_mcart_1(X10) = X11 | k1_mcart_1(X10) = X12 | k1_mcart_1(X10) = X9) )),
% 0.38/0.68    inference(resolution,[],[f48,f22])).
% 0.38/0.68  fof(f22,plain,(
% 0.38/0.68    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.38/0.68    inference(cnf_transformation,[],[f8])).
% 0.38/0.68  fof(f8,plain,(
% 0.38/0.68    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.38/0.68    inference(ennf_transformation,[],[f4])).
% 0.38/0.68  fof(f4,axiom,(
% 0.38/0.68    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.38/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.38/0.68  fof(f48,plain,(
% 0.38/0.68    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 0.38/0.68    inference(equality_resolution,[],[f41])).
% 0.38/0.68  fof(f41,plain,(
% 0.38/0.68    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.38/0.68    inference(definition_unfolding,[],[f24,f21])).
% 0.38/0.68  fof(f24,plain,(
% 0.38/0.68    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.38/0.68    inference(cnf_transformation,[],[f16])).
% 0.38/0.68  fof(f16,plain,(
% 0.38/0.68    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.38/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f15])).
% 0.38/0.68  fof(f15,plain,(
% 0.38/0.68    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 0.38/0.68    introduced(choice_axiom,[])).
% 0.38/0.68  fof(f14,plain,(
% 0.38/0.68    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.38/0.68    inference(rectify,[],[f13])).
% 0.38/0.68  fof(f13,plain,(
% 0.38/0.68    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.38/0.68    inference(flattening,[],[f12])).
% 0.38/0.68  fof(f12,plain,(
% 0.38/0.68    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.38/0.68    inference(nnf_transformation,[],[f9])).
% 0.38/0.68  fof(f9,plain,(
% 0.38/0.68    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.38/0.68    inference(ennf_transformation,[],[f1])).
% 0.38/0.68  fof(f1,axiom,(
% 0.38/0.68    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.38/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.38/0.68  fof(f65,plain,(
% 0.38/0.68    spl5_2),
% 0.38/0.68    inference(avatar_contradiction_clause,[],[f64])).
% 0.38/0.68  fof(f64,plain,(
% 0.38/0.68    $false | spl5_2),
% 0.38/0.68    inference(resolution,[],[f63,f33])).
% 0.38/0.68  fof(f63,plain,(
% 0.38/0.68    ( ! [X0] : (~r2_hidden(sK0,k2_zfmisc_1(X0,sK3))) ) | spl5_2),
% 0.38/0.68    inference(resolution,[],[f23,f56])).
% 0.38/0.68  fof(f56,plain,(
% 0.38/0.68    ~r2_hidden(k2_mcart_1(sK0),sK3) | spl5_2),
% 0.38/0.68    inference(avatar_component_clause,[],[f54])).
% 0.38/0.68  fof(f54,plain,(
% 0.38/0.68    spl5_2 <=> r2_hidden(k2_mcart_1(sK0),sK3)),
% 0.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.38/0.68  fof(f23,plain,(
% 0.38/0.68    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.38/0.68    inference(cnf_transformation,[],[f8])).
% 0.38/0.68  fof(f62,plain,(
% 0.38/0.68    ~spl5_3 | ~spl5_2),
% 0.38/0.68    inference(avatar_split_clause,[],[f18,f54,f59])).
% 0.38/0.68  fof(f18,plain,(
% 0.38/0.68    ~r2_hidden(k2_mcart_1(sK0),sK3) | sK1 != k1_mcart_1(sK0)),
% 0.38/0.68    inference(cnf_transformation,[],[f11])).
% 0.38/0.68  fof(f57,plain,(
% 0.38/0.68    ~spl5_1 | ~spl5_2),
% 0.38/0.68    inference(avatar_split_clause,[],[f19,f54,f50])).
% 0.38/0.68  fof(f19,plain,(
% 0.38/0.68    ~r2_hidden(k2_mcart_1(sK0),sK3) | sK2 != k1_mcart_1(sK0)),
% 0.38/0.68    inference(cnf_transformation,[],[f11])).
% 0.38/0.68  % SZS output end Proof for theBenchmark
% 0.38/0.68  % (23685)------------------------------
% 0.38/0.68  % (23685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.68  % (23685)Termination reason: Refutation
% 0.38/0.68  
% 0.38/0.68  % (23685)Memory used [KB]: 10746
% 0.38/0.68  % (23685)Time elapsed: 0.102 s
% 0.38/0.68  % (23685)------------------------------
% 0.38/0.68  % (23685)------------------------------
% 0.38/0.68  % (23704)Refutation not found, incomplete strategy% (23704)------------------------------
% 0.38/0.68  % (23704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.68  % (23704)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.68  
% 0.38/0.68  % (23704)Memory used [KB]: 1663
% 0.38/0.68  % (23704)Time elapsed: 0.098 s
% 0.38/0.68  % (23704)------------------------------
% 0.38/0.68  % (23704)------------------------------
% 0.38/0.68  % (23712)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.38/0.68  % (23708)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.38/0.68  % (23683)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.38/0.68  % (23493)Success in time 0.32 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:46:06 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 (  91 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 ( 307 expanded)
%              Number of equality atoms :   18 (  52 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f502,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f332,f333,f496])).

fof(f496,plain,
    ( ~ spl5_1
    | spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f491,f38,f47,f38])).

fof(f47,plain,
    ( spl5_3
  <=> r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f38,plain,
    ( spl5_1
  <=> r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f491,plain,
    ( r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1)))
    | ~ r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f89,f81])).

fof(f81,plain,
    ( r2_hidden(sK4(sK1,sK2(sK0,k1_setfam_1(sK1))),sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f32,f40])).

fof(f40,plain,
    ( r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f32,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK4(sK1,X0),sK1) ) ),
    inference(resolution,[],[f22,f28])).

fof(f28,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK4(X0,X4),X0)
      | ~ r2_hidden(X4,X1)
      | ~ r2_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r2_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(X3,sK3(X0,X1))
              | ~ r2_hidden(X3,X0) )
          & r2_hidden(sK3(X0,X1),X1) ) )
      & ( ! [X4] :
            ( ( r1_tarski(sK4(X0,X4),X4)
              & r2_hidden(sK4(X0,X4),X0) )
            | ~ r2_hidden(X4,X1) )
        | ~ r2_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f20,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X2)
              | ~ r2_hidden(X3,X0) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r1_tarski(X3,sK3(X0,X1))
            | ~ r2_hidden(X3,X0) )
        & r2_hidden(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( r1_tarski(X5,X4)
          & r2_hidden(X5,X0) )
     => ( r1_tarski(sK4(X0,X4),X4)
        & r2_hidden(sK4(X0,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X3,X2)
                | ~ r2_hidden(X3,X0) )
            & r2_hidden(X2,X1) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X5,X4)
                & r2_hidden(X5,X0) )
            | ~ r2_hidden(X4,X1) )
        | ~ r2_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X3,X2)
                | ~ r2_hidden(X3,X0) )
            & r2_hidden(X2,X1) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X3,X2)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
        | ~ r2_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X3,X2)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X3,X2)
                  & r2_hidden(X3,X0) )
            & r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_setfam_1)).

fof(f22,plain,(
    r2_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    & k1_xboole_0 != sK0
    & r2_setfam_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & r2_setfam_1(X1,X0) )
   => ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
      & k1_xboole_0 != sK0
      & r2_setfam_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r2_setfam_1(X1,X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r2_setfam_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_setfam_1(X1,X0)
       => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( r2_setfam_1(X1,X0)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_setfam_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK1,X0),X1)
      | r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f33,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f33,plain,(
    ! [X1] :
      ( r1_tarski(sK4(sK1,X1),X1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f22,f29])).

fof(f29,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(sK4(X0,X4),X4)
      | ~ r2_hidden(X4,X1)
      | ~ r2_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f333,plain,
    ( ~ spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f331,f42,f47])).

fof(f42,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f331,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1))) ),
    inference(resolution,[],[f24,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f24,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f332,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f330,f42,f38])).

fof(f330,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0) ),
    inference(resolution,[],[f24,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f23,f44])).

fof(f44,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f23,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.46  % (15270)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.47  % (15278)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.48  % (15270)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.49  % (15265)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f502,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(avatar_sat_refutation,[],[f57,f332,f333,f496])).
% 0.19/0.49  fof(f496,plain,(
% 0.19/0.49    ~spl5_1 | spl5_3 | ~spl5_1),
% 0.19/0.49    inference(avatar_split_clause,[],[f491,f38,f47,f38])).
% 0.19/0.49  fof(f47,plain,(
% 0.19/0.49    spl5_3 <=> r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.49  fof(f38,plain,(
% 0.19/0.49    spl5_1 <=> r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.49  fof(f491,plain,(
% 0.19/0.49    r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1))) | ~r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0) | ~spl5_1),
% 0.19/0.49    inference(resolution,[],[f89,f81])).
% 0.19/0.49  fof(f81,plain,(
% 0.19/0.49    r2_hidden(sK4(sK1,sK2(sK0,k1_setfam_1(sK1))),sK1) | ~spl5_1),
% 0.19/0.49    inference(resolution,[],[f32,f40])).
% 0.19/0.49  fof(f40,plain,(
% 0.19/0.49    r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0) | ~spl5_1),
% 0.19/0.49    inference(avatar_component_clause,[],[f38])).
% 0.19/0.49  fof(f32,plain,(
% 0.19/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(sK4(sK1,X0),sK1)) )),
% 0.19/0.49    inference(resolution,[],[f22,f28])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ( ! [X4,X0,X1] : (r2_hidden(sK4(X0,X4),X0) | ~r2_hidden(X4,X1) | ~r2_setfam_1(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ! [X0,X1] : ((r2_setfam_1(X0,X1) | (! [X3] : (~r1_tarski(X3,sK3(X0,X1)) | ~r2_hidden(X3,X0)) & r2_hidden(sK3(X0,X1),X1))) & (! [X4] : ((r1_tarski(sK4(X0,X4),X4) & r2_hidden(sK4(X0,X4),X0)) | ~r2_hidden(X4,X1)) | ~r2_setfam_1(X0,X1)))),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f20,f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~r2_hidden(X3,X0)) & r2_hidden(X2,X1)) => (! [X3] : (~r1_tarski(X3,sK3(X0,X1)) | ~r2_hidden(X3,X0)) & r2_hidden(sK3(X0,X1),X1)))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X4,X0] : (? [X5] : (r1_tarski(X5,X4) & r2_hidden(X5,X0)) => (r1_tarski(sK4(X0,X4),X4) & r2_hidden(sK4(X0,X4),X0)))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0,X1] : ((r2_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~r2_hidden(X3,X0)) & r2_hidden(X2,X1))) & (! [X4] : (? [X5] : (r1_tarski(X5,X4) & r2_hidden(X5,X0)) | ~r2_hidden(X4,X1)) | ~r2_setfam_1(X0,X1)))),
% 0.19/0.49    inference(rectify,[],[f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ! [X0,X1] : ((r2_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~r2_hidden(X3,X0)) & r2_hidden(X2,X1))) & (! [X2] : (? [X3] : (r1_tarski(X3,X2) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) | ~r2_setfam_1(X0,X1)))),
% 0.19/0.49    inference(nnf_transformation,[],[f12])).
% 0.19/0.49  fof(f12,plain,(
% 0.19/0.49    ! [X0,X1] : (r2_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X2) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)))),
% 0.19/0.49    inference(ennf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1] : (r2_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X3,X2) & r2_hidden(X3,X0)) & r2_hidden(X2,X1)))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_setfam_1)).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    r2_setfam_1(sK1,sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) & k1_xboole_0 != sK0 & r2_setfam_1(sK1,sK0)),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0 & r2_setfam_1(X1,X0)) => (~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) & k1_xboole_0 != sK0 & r2_setfam_1(sK1,sK0))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f7,plain,(
% 0.19/0.49    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0 & r2_setfam_1(X1,X0))),
% 0.19/0.49    inference(flattening,[],[f6])).
% 0.19/0.49  fof(f6,plain,(
% 0.19/0.49    ? [X0,X1] : ((~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0) & r2_setfam_1(X1,X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1] : (r2_setfam_1(X1,X0) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.19/0.49    inference(negated_conjecture,[],[f4])).
% 0.19/0.49  fof(f4,conjecture,(
% 0.19/0.49    ! [X0,X1] : (r2_setfam_1(X1,X0) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_setfam_1)).
% 0.19/0.49  fof(f89,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r2_hidden(sK4(sK1,X0),X1) | r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,sK0)) )),
% 0.19/0.49    inference(resolution,[],[f33,f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 0.19/0.49    inference(flattening,[],[f8])).
% 0.19/0.49  fof(f8,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 0.19/0.49    inference(ennf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    ( ! [X1] : (r1_tarski(sK4(sK1,X1),X1) | ~r2_hidden(X1,sK0)) )),
% 0.19/0.49    inference(resolution,[],[f22,f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ( ! [X4,X0,X1] : (r1_tarski(sK4(X0,X4),X4) | ~r2_hidden(X4,X1) | ~r2_setfam_1(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f21])).
% 0.19/0.49  fof(f333,plain,(
% 0.19/0.49    ~spl5_3 | spl5_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f331,f42,f47])).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    spl5_2 <=> k1_xboole_0 = sK0),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.49  fof(f331,plain,(
% 0.19/0.49    k1_xboole_0 = sK0 | ~r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1)))),
% 0.19/0.49    inference(resolution,[],[f24,f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK2(X0,X1))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f11,plain,(
% 0.19/0.49    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.19/0.49    inference(flattening,[],[f10])).
% 0.19/0.49  fof(f10,plain,(
% 0.19/0.49    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    ~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f332,plain,(
% 0.19/0.49    spl5_1 | spl5_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f330,f42,f38])).
% 0.19/0.49  fof(f330,plain,(
% 0.19/0.49    k1_xboole_0 = sK0 | r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0)),
% 0.19/0.49    inference(resolution,[],[f24,f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK2(X0,X1),X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f57,plain,(
% 0.19/0.49    ~spl5_2),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f53])).
% 0.19/0.49  fof(f53,plain,(
% 0.19/0.49    $false | ~spl5_2),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f23,f44])).
% 0.19/0.49  fof(f44,plain,(
% 0.19/0.49    k1_xboole_0 = sK0 | ~spl5_2),
% 0.19/0.49    inference(avatar_component_clause,[],[f42])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    k1_xboole_0 != sK0),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (15270)------------------------------
% 0.19/0.49  % (15270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (15270)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (15270)Memory used [KB]: 6268
% 0.19/0.49  % (15270)Time elapsed: 0.080 s
% 0.19/0.49  % (15270)------------------------------
% 0.19/0.49  % (15270)------------------------------
% 0.19/0.50  % (15259)Success in time 0.145 s
%------------------------------------------------------------------------------

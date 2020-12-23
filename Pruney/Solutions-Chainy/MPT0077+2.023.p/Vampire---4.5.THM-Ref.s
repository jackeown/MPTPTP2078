%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 161 expanded)
%              Number of leaves         :    9 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  242 ( 799 expanded)
%              Number of equality atoms :   12 (  30 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1014,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f61,f120,f138,f1013])).

fof(f1013,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f1012])).

fof(f1012,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f789,f139])).

fof(f139,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f53,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f7,f10])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f53,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl6_2
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f789,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ spl6_1
    | spl6_2
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f142,f141,f34])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f15])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f141,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | spl6_2
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f59,f140,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f140,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f53,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f59,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl6_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f142,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | ~ spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f50,f140,f25])).

fof(f50,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl6_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f138,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f129,f126])).

fof(f126,plain,
    ( ! [X0] : r2_hidden(sK3(sK0,sK2),k2_xboole_0(X0,sK2))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f121,f32])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f121,plain,
    ( r2_hidden(sK3(sK0,sK2),sK2)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f49,f24])).

fof(f49,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f129,plain,
    ( ~ r2_hidden(sK3(sK0,sK2),k2_xboole_0(sK1,sK2))
    | spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f54,f122,f25])).

fof(f122,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f49,f23])).

fof(f54,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f120,plain,
    ( ~ spl6_2
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f113,f70])).

fof(f70,plain,
    ( ! [X0] : r2_hidden(sK3(sK0,sK1),k2_xboole_0(sK1,X0))
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f64,f33])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f58,f24])).

fof(f58,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f113,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),k2_xboole_0(sK1,sK2))
    | ~ spl6_2
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f63,f54,f25])).

fof(f63,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f58,f23])).

fof(f61,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f17,f48,f57,f52])).

fof(f17,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
        & ( ~ r1_xboole_0(sK0,sK2)
          | ~ r1_xboole_0(sK0,sK1) ) )
      | ( r1_xboole_0(sK0,sK2)
        & r1_xboole_0(sK0,sK1)
        & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f60,plain,
    ( spl6_3
    | spl6_2 ),
    inference(avatar_split_clause,[],[f21,f52,f57])).

fof(f21,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f22,f52,f48])).

fof(f22,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:36:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (8885)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (8887)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (8872)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (8885)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f1014,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f55,f60,f61,f120,f138,f1013])).
% 0.20/0.49  fof(f1013,plain,(
% 0.20/0.49    ~spl6_1 | spl6_2 | ~spl6_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f1012])).
% 0.20/0.49  fof(f1012,plain,(
% 0.20/0.49    $false | (~spl6_1 | spl6_2 | ~spl6_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f789,f139])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) | spl6_2),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f53,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f7,f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,plain,(
% 0.20/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(rectify,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl6_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    spl6_2 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.49  fof(f789,plain,(
% 0.20/0.49    ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) | (~spl6_1 | spl6_2 | ~spl6_3)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f142,f141,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_xboole_0(X0,X1)) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(rectify,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) | (spl6_2 | ~spl6_3)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f59,f140,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) | spl6_2),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f53,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    r1_xboole_0(sK0,sK1) | ~spl6_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    spl6_3 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) | (~spl6_1 | spl6_2)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f50,f140,f25])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    r1_xboole_0(sK0,sK2) | ~spl6_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    spl6_1 <=> r1_xboole_0(sK0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    spl6_1 | ~spl6_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f137])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    $false | (spl6_1 | ~spl6_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f129,f126])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK3(sK0,sK2),k2_xboole_0(X0,sK2))) ) | spl6_1),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f121,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    r2_hidden(sK3(sK0,sK2),sK2) | spl6_1),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f49,f24])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,sK2) | spl6_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f48])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    ~r2_hidden(sK3(sK0,sK2),k2_xboole_0(sK1,sK2)) | (spl6_1 | ~spl6_2)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f54,f122,f25])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    r2_hidden(sK3(sK0,sK2),sK0) | spl6_1),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f49,f23])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl6_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f52])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    ~spl6_2 | spl6_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f119])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    $false | (~spl6_2 | spl6_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f113,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK3(sK0,sK1),k2_xboole_0(sK1,X0))) ) | spl6_3),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f64,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    r2_hidden(sK3(sK0,sK1),sK1) | spl6_3),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f58,f24])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,sK1) | spl6_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f57])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    ~r2_hidden(sK3(sK0,sK1),k2_xboole_0(sK1,sK2)) | (~spl6_2 | spl6_3)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f63,f54,f25])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    r2_hidden(sK3(sK0,sK1),sK0) | spl6_3),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f58,f23])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ~spl6_2 | ~spl6_3 | ~spl6_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f17,f48,f57,f52])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f6,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.49    inference(negated_conjecture,[],[f3])).
% 0.20/0.49  fof(f3,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    spl6_3 | spl6_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f21,f52,f57])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    spl6_1 | spl6_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f22,f52,f48])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (8885)------------------------------
% 0.20/0.49  % (8885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8885)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (8885)Memory used [KB]: 11001
% 0.20/0.49  % (8885)Time elapsed: 0.024 s
% 0.20/0.49  % (8885)------------------------------
% 0.20/0.49  % (8885)------------------------------
% 0.20/0.50  % (8863)Success in time 0.133 s
%------------------------------------------------------------------------------

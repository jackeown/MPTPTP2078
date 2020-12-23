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
% DateTime   : Thu Dec  3 12:51:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  82 expanded)
%              Number of leaves         :   13 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  182 ( 300 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f42,f46,f50,f56,f61,f66])).

fof(f66,plain,
    ( ~ spl4_2
    | spl4_1
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f64,f59,f36,f40])).

fof(f40,plain,
    ( spl4_2
  <=> r2_hidden(sK2,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f36,plain,
    ( spl4_1
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f59,plain,
    ( spl4_6
  <=> k2_relat_1(sK1) = k3_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f64,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(sK1))
    | spl4_1
    | ~ spl4_6 ),
    inference(resolution,[],[f63,f37])).

fof(f37,plain,
    ( ~ r2_hidden(sK2,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f63,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK0)
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl4_6 ),
    inference(superposition,[],[f33,f60])).

fof(f60,plain,
    ( k2_relat_1(sK1) = k3_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f61,plain,
    ( spl4_6
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f57,f54,f59])).

fof(f54,plain,
    ( spl4_5
  <=> r1_tarski(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f57,plain,
    ( k2_relat_1(sK1) = k3_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f55,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f55,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f56,plain,
    ( spl4_5
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f52,f48,f44,f54])).

fof(f44,plain,
    ( spl4_3
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f48,plain,
    ( spl4_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f52,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f51,f45])).

fof(f45,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f51,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK1,X0)
        | r1_tarski(k2_relat_1(sK1),X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f23,f49])).

fof(f49,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f50,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f19,f48])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r2_hidden(sK2,sK0)
    & r2_hidden(sK2,k2_relat_1(sK1))
    & v5_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,k2_relat_1(X1)) )
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(X2,sK0)
          & r2_hidden(X2,k2_relat_1(sK1)) )
      & v5_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X2] :
        ( ~ r2_hidden(X2,sK0)
        & r2_hidden(X2,k2_relat_1(sK1)) )
   => ( ~ r2_hidden(sK2,sK0)
      & r2_hidden(sK2,k2_relat_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,k2_relat_1(X1)) )
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,k2_relat_1(X1)) )
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( r2_hidden(X2,k2_relat_1(X1))
           => r2_hidden(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

fof(f46,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    r2_hidden(sK2,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f22,f36])).

fof(f22,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (11376)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.43  % (11376)Refutation not found, incomplete strategy% (11376)------------------------------
% 0.21/0.43  % (11376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (11376)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.43  
% 0.21/0.43  % (11376)Memory used [KB]: 10490
% 0.21/0.43  % (11376)Time elapsed: 0.028 s
% 0.21/0.43  % (11376)------------------------------
% 0.21/0.43  % (11376)------------------------------
% 0.21/0.46  % (11362)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.46  % (11362)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f38,f42,f46,f50,f56,f61,f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ~spl4_2 | spl4_1 | ~spl4_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f64,f59,f36,f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    spl4_2 <=> r2_hidden(sK2,k2_relat_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    spl4_1 <=> r2_hidden(sK2,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    spl4_6 <=> k2_relat_1(sK1) = k3_xboole_0(k2_relat_1(sK1),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ~r2_hidden(sK2,k2_relat_1(sK1)) | (spl4_1 | ~spl4_6)),
% 0.21/0.46    inference(resolution,[],[f63,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ~r2_hidden(sK2,sK0) | spl4_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f36])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X1] : (r2_hidden(X1,sK0) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | ~spl4_6),
% 0.21/0.46    inference(superposition,[],[f33,f60])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    k2_relat_1(sK1) = k3_xboole_0(k2_relat_1(sK1),sK0) | ~spl4_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f59])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 0.21/0.46    inference(equality_resolution,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.46    inference(rectify,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.46    inference(flattening,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.46    inference(nnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    spl4_6 | ~spl4_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f57,f54,f59])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    spl4_5 <=> r1_tarski(k2_relat_1(sK1),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    k2_relat_1(sK1) = k3_xboole_0(k2_relat_1(sK1),sK0) | ~spl4_5),
% 0.21/0.46    inference(resolution,[],[f55,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    r1_tarski(k2_relat_1(sK1),sK0) | ~spl4_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f54])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    spl4_5 | ~spl4_3 | ~spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f52,f48,f44,f54])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    spl4_3 <=> v5_relat_1(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    spl4_4 <=> v1_relat_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    r1_tarski(k2_relat_1(sK1),sK0) | (~spl4_3 | ~spl4_4)),
% 0.21/0.46    inference(resolution,[],[f51,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    v5_relat_1(sK1,sK0) | ~spl4_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f44])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ( ! [X0] : (~v5_relat_1(sK1,X0) | r1_tarski(k2_relat_1(sK1),X0)) ) | ~spl4_4),
% 0.21/0.46    inference(resolution,[],[f23,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    v1_relat_1(sK1) | ~spl4_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f48])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f19,f48])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    v1_relat_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    (~r2_hidden(sK2,sK0) & r2_hidden(sK2,k2_relat_1(sK1))) & v5_relat_1(sK1,sK0) & v1_relat_1(sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11,f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,k2_relat_1(X1))) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => (? [X2] : (~r2_hidden(X2,sK0) & r2_hidden(X2,k2_relat_1(sK1))) & v5_relat_1(sK1,sK0) & v1_relat_1(sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ? [X2] : (~r2_hidden(X2,sK0) & r2_hidden(X2,k2_relat_1(sK1))) => (~r2_hidden(sK2,sK0) & r2_hidden(sK2,k2_relat_1(sK1)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,k2_relat_1(X1))) & v5_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f6])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,k2_relat_1(X1))) & (v5_relat_1(X1,X0) & v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 0.21/0.46    inference(negated_conjecture,[],[f4])).
% 0.21/0.46  fof(f4,conjecture,(
% 0.21/0.46    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    spl4_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f20,f44])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    v5_relat_1(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    spl4_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f21,f40])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    r2_hidden(sK2,k2_relat_1(sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ~spl4_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f36])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ~r2_hidden(sK2,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (11362)------------------------------
% 0.21/0.46  % (11362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (11362)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (11362)Memory used [KB]: 10618
% 0.21/0.46  % (11362)Time elapsed: 0.026 s
% 0.21/0.46  % (11362)------------------------------
% 0.21/0.46  % (11362)------------------------------
% 0.21/0.46  % (11355)Success in time 0.107 s
%------------------------------------------------------------------------------

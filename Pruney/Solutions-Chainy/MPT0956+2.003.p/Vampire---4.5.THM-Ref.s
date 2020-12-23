%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of leaves         :    8 (  10 expanded)
%              Depth                    :   14
%              Number of atoms          :  145 ( 149 expanded)
%              Number of equality atoms :   26 (  26 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f48])).

fof(f48,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f40,f46])).

fof(f46,plain,(
    ! [X0] : r1_relat_2(k1_wellord2(X0),X0) ),
    inference(global_subsumption,[],[f20,f21,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r1_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_2(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f22,f44])).

fof(f44,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f21,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK1(X0,X1),sK2(X0,X1))
              | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
            & ( r1_tarski(sK1(X0,X1),sK2(X0,X1))
              | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
            & r2_hidden(sK2(X0,X1),X0)
            & r2_hidden(sK1(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK1(X0,X1),sK2(X0,X1))
          | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
        & ( r1_tarski(sK1(X0,X1),sK2(X0,X1))
          | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
        & r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f22,plain,(
    ! [X0] :
      ( r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ~ r1_relat_2(X0,k3_relat_1(X0)) )
        & ( r1_relat_2(X0,k3_relat_1(X0))
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_relat_2)).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f20,plain,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord2)).

fof(f40,plain,
    ( ~ r1_relat_2(k1_wellord2(sK0),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_1
  <=> r1_relat_2(k1_wellord2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f41,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    ~ r1_relat_2(k1_wellord2(sK0),sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ~ r1_relat_2(k1_wellord2(sK0),sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f11])).

fof(f11,plain,
    ( ? [X0] : ~ r1_relat_2(k1_wellord2(X0),X0)
   => ~ r1_relat_2(k1_wellord2(sK0),sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : ~ r1_relat_2(k1_wellord2(X0),X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r1_relat_2(k1_wellord2(X0),X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : r1_relat_2(k1_wellord2(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (14630)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.41  % (14630)Refutation not found, incomplete strategy% (14630)------------------------------
% 0.20/0.41  % (14630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (14630)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.41  
% 0.20/0.41  % (14630)Memory used [KB]: 1535
% 0.20/0.41  % (14630)Time elapsed: 0.002 s
% 0.20/0.41  % (14630)------------------------------
% 0.20/0.41  % (14630)------------------------------
% 0.20/0.44  % (14631)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (14624)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (14617)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (14617)Refutation not found, incomplete strategy% (14617)------------------------------
% 0.20/0.48  % (14617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (14617)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (14617)Memory used [KB]: 6140
% 0.20/0.48  % (14617)Time elapsed: 0.064 s
% 0.20/0.48  % (14617)------------------------------
% 0.20/0.48  % (14617)------------------------------
% 0.20/0.48  % (14626)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (14625)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (14632)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (14620)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (14632)Refutation not found, incomplete strategy% (14632)------------------------------
% 0.20/0.49  % (14632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (14632)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (14632)Memory used [KB]: 6012
% 0.20/0.49  % (14632)Time elapsed: 0.076 s
% 0.20/0.49  % (14632)------------------------------
% 0.20/0.49  % (14632)------------------------------
% 0.20/0.49  % (14620)Refutation not found, incomplete strategy% (14620)------------------------------
% 0.20/0.49  % (14620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (14620)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (14620)Memory used [KB]: 10490
% 0.20/0.49  % (14620)Time elapsed: 0.081 s
% 0.20/0.49  % (14620)------------------------------
% 0.20/0.49  % (14620)------------------------------
% 0.20/0.49  % (14623)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (14623)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f41,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    spl3_1),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    $false | spl3_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f40,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X0] : (r1_relat_2(k1_wellord2(X0),X0)) )),
% 0.20/0.50    inference(global_subsumption,[],[f20,f21,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0] : (r1_relat_2(k1_wellord2(X0),X0) | ~v1_relat_2(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.50    inference(superposition,[],[f22,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.20/0.50    inference(global_subsumption,[],[f21,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.50    inference(equality_resolution,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r1_tarski(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r1_tarski(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(rectify,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X0] : (r1_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0] : (((v1_relat_2(X0) | ~r1_relat_2(X0,k3_relat_1(X0))) & (r1_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ! [X0] : ((v1_relat_2(X0) <=> r1_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> r1_relat_2(X0,k3_relat_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_relat_2)).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_2(k1_wellord2(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : v1_relat_2(k1_wellord2(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord2)).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ~r1_relat_2(k1_wellord2(sK0),sK0) | spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    spl3_1 <=> r1_relat_2(k1_wellord2(sK0),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ~spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f19,f39])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ~r1_relat_2(k1_wellord2(sK0),sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ~r1_relat_2(k1_wellord2(sK0),sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ? [X0] : ~r1_relat_2(k1_wellord2(X0),X0) => ~r1_relat_2(k1_wellord2(sK0),sK0)),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f7,plain,(
% 0.20/0.50    ? [X0] : ~r1_relat_2(k1_wellord2(X0),X0)),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,negated_conjecture,(
% 0.20/0.50    ~! [X0] : r1_relat_2(k1_wellord2(X0),X0)),
% 0.20/0.50    inference(negated_conjecture,[],[f5])).
% 0.20/0.50  fof(f5,conjecture,(
% 0.20/0.50    ! [X0] : r1_relat_2(k1_wellord2(X0),X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord2)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (14623)------------------------------
% 0.20/0.50  % (14623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (14623)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (14623)Memory used [KB]: 10618
% 0.20/0.50  % (14623)Time elapsed: 0.075 s
% 0.20/0.50  % (14623)------------------------------
% 0.20/0.50  % (14623)------------------------------
% 0.20/0.50  % (14616)Success in time 0.142 s
%------------------------------------------------------------------------------

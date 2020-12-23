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
% DateTime   : Thu Dec  3 12:52:16 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   40 (  50 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :   14
%              Number of atoms          :  174 ( 195 expanded)
%              Number of equality atoms :   56 (  63 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f70])).

% (8826)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f70,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f65,f45])).

fof(f45,plain,
    ( sK0 != k1_funct_1(k6_relat_1(sK1),sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_2
  <=> sK0 = k1_funct_1(k6_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f65,plain,
    ( sK0 = k1_funct_1(k6_relat_1(sK1),sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f61,f40])).

fof(f40,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k1_funct_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(resolution,[],[f55,f47])).

fof(f47,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0) ) ),
    inference(subsumption_resolution,[],[f33,f21])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f33,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK2(X0,X1) != sK3(X0,X1)
              | ~ r2_hidden(sK2(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & ( ( sK2(X0,X1) = sK3(X0,X1)
                & r2_hidden(sK2(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK2(X0,X1) != sK3(X0,X1)
          | ~ r2_hidden(sK2(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( ( sK2(X0,X1) = sK3(X0,X1)
            & r2_hidden(sK2(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
      | k1_funct_1(k6_relat_1(X2),X0) = X1 ) ),
    inference(subsumption_resolution,[],[f54,f21])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
      | k1_funct_1(k6_relat_1(X2),X0) = X1
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f30,f22])).

fof(f22,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f46,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    sK0 != k1_funct_1(k6_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( sK0 != k1_funct_1(k6_relat_1(sK1),sK0)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( k1_funct_1(k6_relat_1(X1),X0) != X0
        & r2_hidden(X0,X1) )
   => ( sK0 != k1_funct_1(k6_relat_1(sK1),sK0)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) != X0
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

fof(f41,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:29:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.23/0.52  % (8843)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.53  % (8824)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.53  % (8824)Refutation found. Thanks to Tanya!
% 0.23/0.53  % SZS status Theorem for theBenchmark
% 0.23/0.53  % (8836)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f71,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(avatar_sat_refutation,[],[f41,f46,f70])).
% 0.23/0.53  % (8826)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.53  fof(f70,plain,(
% 0.23/0.53    ~spl4_1 | spl4_2),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f69])).
% 0.23/0.53  fof(f69,plain,(
% 0.23/0.53    $false | (~spl4_1 | spl4_2)),
% 0.23/0.53    inference(subsumption_resolution,[],[f65,f45])).
% 0.23/0.53  fof(f45,plain,(
% 0.23/0.53    sK0 != k1_funct_1(k6_relat_1(sK1),sK0) | spl4_2),
% 0.23/0.53    inference(avatar_component_clause,[],[f43])).
% 0.23/0.53  fof(f43,plain,(
% 0.23/0.53    spl4_2 <=> sK0 = k1_funct_1(k6_relat_1(sK1),sK0)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.23/0.53  fof(f65,plain,(
% 0.23/0.53    sK0 = k1_funct_1(k6_relat_1(sK1),sK0) | ~spl4_1),
% 0.23/0.53    inference(resolution,[],[f61,f40])).
% 0.23/0.53  fof(f40,plain,(
% 0.23/0.53    r2_hidden(sK0,sK1) | ~spl4_1),
% 0.23/0.53    inference(avatar_component_clause,[],[f38])).
% 0.23/0.53  fof(f38,plain,(
% 0.23/0.53    spl4_1 <=> r2_hidden(sK0,sK1)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.23/0.53  fof(f61,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k1_funct_1(k6_relat_1(X0),X1) = X1) )),
% 0.23/0.53    inference(resolution,[],[f55,f47])).
% 0.23/0.53  fof(f47,plain,(
% 0.23/0.53    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0)) | ~r2_hidden(X5,X0)) )),
% 0.23/0.53    inference(subsumption_resolution,[],[f33,f21])).
% 0.23/0.53  fof(f21,plain,(
% 0.23/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f2])).
% 0.23/0.53  fof(f2,axiom,(
% 0.23/0.53    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.23/0.53  fof(f33,plain,(
% 0.23/0.53    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0)) | ~r2_hidden(X5,X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.23/0.53    inference(equality_resolution,[],[f32])).
% 0.23/0.53  fof(f32,plain,(
% 0.23/0.53    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,X5),X1) | ~r2_hidden(X5,X0) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.23/0.53    inference(equality_resolution,[],[f25])).
% 0.23/0.53  fof(f25,plain,(
% 0.23/0.53    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f16])).
% 0.23/0.53  fof(f16,plain,(
% 0.23/0.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ((sK2(X0,X1) != sK3(X0,X1) | ~r2_hidden(sK2(X0,X1),X0) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & ((sK2(X0,X1) = sK3(X0,X1) & r2_hidden(sK2(X0,X1),X0)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 0.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f15])).
% 0.23/0.53  fof(f15,plain,(
% 0.23/0.53    ! [X1,X0] : (? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1))) => ((sK2(X0,X1) != sK3(X0,X1) | ~r2_hidden(sK2(X0,X1),X0) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & ((sK2(X0,X1) = sK3(X0,X1) & r2_hidden(sK2(X0,X1),X0)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1))))),
% 0.23/0.53    introduced(choice_axiom,[])).
% 0.23/0.53  fof(f14,plain,(
% 0.23/0.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 0.23/0.53    inference(rectify,[],[f13])).
% 0.23/0.53  fof(f13,plain,(
% 0.23/0.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | X2 != X3 | ~r2_hidden(X2,X0)) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 0.23/0.53    inference(flattening,[],[f12])).
% 0.23/0.53  fof(f12,plain,(
% 0.23/0.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : (((X2 != X3 | ~r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | (X2 != X3 | ~r2_hidden(X2,X0))) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 0.23/0.53    inference(nnf_transformation,[],[f7])).
% 0.23/0.53  fof(f7,plain,(
% 0.23/0.53    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f1])).
% 0.23/0.53  fof(f1,axiom,(
% 0.23/0.53    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).
% 0.23/0.53  fof(f55,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2)) | k1_funct_1(k6_relat_1(X2),X0) = X1) )),
% 0.23/0.53    inference(subsumption_resolution,[],[f54,f21])).
% 0.23/0.53  fof(f54,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2)) | k1_funct_1(k6_relat_1(X2),X0) = X1 | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.23/0.53    inference(resolution,[],[f30,f22])).
% 0.23/0.53  fof(f22,plain,(
% 0.23/0.53    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f2])).
% 0.23/0.53  fof(f30,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f18])).
% 0.23/0.53  fof(f18,plain,(
% 0.23/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.23/0.53    inference(flattening,[],[f17])).
% 0.23/0.53  fof(f17,plain,(
% 0.23/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.23/0.53    inference(nnf_transformation,[],[f9])).
% 0.23/0.53  fof(f9,plain,(
% 0.23/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.23/0.53    inference(flattening,[],[f8])).
% 0.23/0.53  fof(f8,plain,(
% 0.23/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.23/0.53    inference(ennf_transformation,[],[f3])).
% 0.23/0.53  fof(f3,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.23/0.53  fof(f46,plain,(
% 0.23/0.53    ~spl4_2),
% 0.23/0.53    inference(avatar_split_clause,[],[f20,f43])).
% 0.23/0.53  fof(f20,plain,(
% 0.23/0.53    sK0 != k1_funct_1(k6_relat_1(sK1),sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f11])).
% 0.23/0.53  fof(f11,plain,(
% 0.23/0.53    sK0 != k1_funct_1(k6_relat_1(sK1),sK0) & r2_hidden(sK0,sK1)),
% 0.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f10])).
% 0.23/0.53  fof(f10,plain,(
% 0.23/0.53    ? [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) != X0 & r2_hidden(X0,X1)) => (sK0 != k1_funct_1(k6_relat_1(sK1),sK0) & r2_hidden(sK0,sK1))),
% 0.23/0.53    introduced(choice_axiom,[])).
% 0.23/0.53  fof(f6,plain,(
% 0.23/0.53    ? [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) != X0 & r2_hidden(X0,X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f5])).
% 0.23/0.53  fof(f5,negated_conjecture,(
% 0.23/0.53    ~! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 0.23/0.53    inference(negated_conjecture,[],[f4])).
% 0.23/0.53  fof(f4,conjecture,(
% 0.23/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).
% 0.23/0.53  fof(f41,plain,(
% 0.23/0.53    spl4_1),
% 0.23/0.53    inference(avatar_split_clause,[],[f19,f38])).
% 0.23/0.53  fof(f19,plain,(
% 0.23/0.53    r2_hidden(sK0,sK1)),
% 0.23/0.53    inference(cnf_transformation,[],[f11])).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (8824)------------------------------
% 0.23/0.53  % (8824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (8824)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (8824)Memory used [KB]: 6140
% 0.23/0.53  % (8824)Time elapsed: 0.098 s
% 0.23/0.53  % (8824)------------------------------
% 0.23/0.53  % (8824)------------------------------
% 0.23/0.53  % (8821)Success in time 0.159 s
%------------------------------------------------------------------------------

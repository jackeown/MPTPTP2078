%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 831 expanded)
%              Number of leaves         :   21 ( 314 expanded)
%              Depth                    :   25
%              Number of atoms          :  731 (8262 expanded)
%              Number of equality atoms :   52 (  70 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f78,f166,f222,f235,f243,f245,f259,f270,f285])).

fof(f285,plain,
    ( ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f274,f68])).

fof(f68,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f63])).

% (1132)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% (1131)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (1105)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f63,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f274,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f71,f121])).

fof(f121,plain,
    ( sK2 = sK3
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_4
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f71,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_1
  <=> r2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f270,plain,
    ( spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f265,f160,f157])).

fof(f157,plain,
    ( spl4_6
  <=> ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK2)
        | ~ m1_orders_2(sK2,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f160,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f265,plain,(
    ! [X2] :
      ( k1_xboole_0 = sK2
      | ~ m1_orders_2(X2,sK0,sK2)
      | ~ m1_orders_2(sK2,sK0,X2) ) ),
    inference(resolution,[],[f45,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | k1_xboole_0 = X0
      | ~ m1_orders_2(X1,sK0,X0)
      | ~ m1_orders_2(X0,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f153,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ m1_orders_2(sK2,sK0,sK3)
      | ~ r2_xboole_0(sK2,sK3) )
    & ( m1_orders_2(sK2,sK0,sK3)
      | r2_xboole_0(sK2,sK3) )
    & m2_orders_2(sK3,sK0,sK1)
    & m2_orders_2(sK2,sK0,sK1)
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f32,f31,f30,f29])).

% (1114)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_orders_2(X2,X0,X3)
                      | ~ r2_xboole_0(X2,X3) )
                    & ( m1_orders_2(X2,X0,X3)
                      | r2_xboole_0(X2,X3) )
                    & m2_orders_2(X3,X0,X1) )
                & m2_orders_2(X2,X0,X1) )
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,sK0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,sK0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,sK0,X1) )
              & m2_orders_2(X2,sK0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_orders_2(X2,sK0,X3)
                  | ~ r2_xboole_0(X2,X3) )
                & ( m1_orders_2(X2,sK0,X3)
                  | r2_xboole_0(X2,X3) )
                & m2_orders_2(X3,sK0,X1) )
            & m2_orders_2(X2,sK0,X1) )
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_orders_2(X2,sK0,X3)
                | ~ r2_xboole_0(X2,X3) )
              & ( m1_orders_2(X2,sK0,X3)
                | r2_xboole_0(X2,X3) )
              & m2_orders_2(X3,sK0,sK1) )
          & m2_orders_2(X2,sK0,sK1) )
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

% (1112)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% (1112)Refutation not found, incomplete strategy% (1112)------------------------------
% (1112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1120)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (1112)Termination reason: Refutation not found, incomplete strategy

% (1112)Memory used [KB]: 10618
% (1112)Time elapsed: 0.093 s
% (1112)------------------------------
% (1112)------------------------------
% (1111)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (1125)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (1105)Refutation not found, incomplete strategy% (1105)------------------------------
% (1105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1105)Termination reason: Refutation not found, incomplete strategy

% (1105)Memory used [KB]: 10618
% (1105)Time elapsed: 0.104 s
% (1105)------------------------------
% (1105)------------------------------
fof(f31,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_orders_2(X2,sK0,X3)
              | ~ r2_xboole_0(X2,X3) )
            & ( m1_orders_2(X2,sK0,X3)
              | r2_xboole_0(X2,X3) )
            & m2_orders_2(X3,sK0,sK1) )
        & m2_orders_2(X2,sK0,sK1) )
   => ( ? [X3] :
          ( ( ~ m1_orders_2(sK2,sK0,X3)
            | ~ r2_xboole_0(sK2,X3) )
          & ( m1_orders_2(sK2,sK0,X3)
            | r2_xboole_0(sK2,X3) )
          & m2_orders_2(X3,sK0,sK1) )
      & m2_orders_2(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( ( ~ m1_orders_2(sK2,sK0,X3)
          | ~ r2_xboole_0(sK2,X3) )
        & ( m1_orders_2(sK2,sK0,X3)
          | r2_xboole_0(sK2,X3) )
        & m2_orders_2(X3,sK0,sK1) )
   => ( ( ~ m1_orders_2(sK2,sK0,sK3)
        | ~ r2_xboole_0(sK2,sK3) )
      & ( m1_orders_2(sK2,sK0,sK3)
        | r2_xboole_0(sK2,sK3) )
      & m2_orders_2(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ( r2_xboole_0(X2,X3)
                    <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( r2_xboole_0(X2,X3)
                  <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | k1_xboole_0 = X0
      | ~ m1_orders_2(X1,sK0,X0)
      | v2_struct_0(sK0)
      | ~ m2_orders_2(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f152,f40])).

fof(f40,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | k1_xboole_0 = X0
      | ~ m1_orders_2(X1,sK0,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m2_orders_2(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f151,f41])).

fof(f41,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | k1_xboole_0 = X0
      | ~ m1_orders_2(X1,sK0,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m2_orders_2(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f150,f42])).

fof(f42,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | k1_xboole_0 = X0
      | ~ m1_orders_2(X1,sK0,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m2_orders_2(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f147,f43])).

fof(f43,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | k1_xboole_0 = X0
      | ~ m1_orders_2(X1,sK0,X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m2_orders_2(X0,sK0,sK1) ) ),
    inference(resolution,[],[f145,f97])).

fof(f97,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f96,f39])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f95,f40])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f94,f41])).

fof(f94,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f93,f42])).

fof(f93,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f92,f43])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f57,f44])).

fof(f44,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X2,X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f55,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_2(X2,X0,X1)
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

fof(f45,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f259,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f252,f65])).

fof(f65,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f252,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f146,f162])).

fof(f162,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f160])).

fof(f146,plain,(
    ~ r1_xboole_0(sK2,sK2) ),
    inference(resolution,[],[f144,f45])).

fof(f144,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ r1_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f143,f45])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X1,sK0,sK1)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(subsumption_resolution,[],[f142,f39])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ r1_xboole_0(X1,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f141,f40])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ r1_xboole_0(X1,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f140,f41])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ r1_xboole_0(X1,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f139,f42])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ r1_xboole_0(X1,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f138,f43])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ r1_xboole_0(X1,X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f51,f44])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ r1_xboole_0(X2,X3)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

fof(f245,plain,
    ( spl4_4
    | spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f123,f74,f70,f119])).

fof(f74,plain,
    ( spl4_2
  <=> m1_orders_2(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f123,plain,
    ( sK2 = sK3
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f112,f72])).

fof(f72,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f112,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK2,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f110,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f110,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f107,f75])).

fof(f75,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f107,plain,(
    ! [X1] :
      ( ~ m1_orders_2(X1,sK0,sK3)
      | r1_tarski(X1,sK3) ) ),
    inference(resolution,[],[f105,f46])).

fof(f46,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X1,sK0,X0)
      | r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f104,f39])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X1,sK0,X0)
      | r1_tarski(X1,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f103,f40])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X1,sK0,X0)
      | r1_tarski(X1,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f102,f41])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X1,sK0,X0)
      | r1_tarski(X1,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f101,f42])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X1,sK0,X0)
      | r1_tarski(X1,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f100,f43])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X1,sK0,X0)
      | r1_tarski(X1,X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f97,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | r1_tarski(X2,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

fof(f243,plain,
    ( spl4_2
    | spl4_10
    | spl4_4 ),
    inference(avatar_split_clause,[],[f211,f119,f215,f74])).

fof(f215,plain,
    ( spl4_10
  <=> m1_orders_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f211,plain,
    ( sK2 = sK3
    | m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3) ),
    inference(resolution,[],[f208,f46])).

fof(f208,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | m1_orders_2(sK2,sK0,X0) ) ),
    inference(resolution,[],[f205,f45])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X1,sK0,sK1)
      | X0 = X1
      | ~ m2_orders_2(X0,sK0,sK1)
      | m1_orders_2(X0,sK0,X1)
      | m1_orders_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f204,f39])).

fof(f204,plain,(
    ! [X0,X1] :
      ( m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | m1_orders_2(X1,sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f203,f40])).

fof(f203,plain,(
    ! [X0,X1] :
      ( m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | m1_orders_2(X1,sK0,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f202,f41])).

fof(f202,plain,(
    ! [X0,X1] :
      ( m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | m1_orders_2(X1,sK0,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f201,f42])).

fof(f201,plain,(
    ! [X0,X1] :
      ( m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | m1_orders_2(X1,sK0,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f200,f43])).

fof(f200,plain,(
    ! [X0,X1] :
      ( m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | m1_orders_2(X1,sK0,X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f53,f44])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | m1_orders_2(X2,X0,X3)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_orders_2(X2,X0,X3)
                      | m1_orders_2(X3,X0,X2) )
                    & ( ~ m1_orders_2(X3,X0,X2)
                      | ~ m1_orders_2(X2,X0,X3) ) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).

fof(f235,plain,
    ( spl4_4
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f234,f126,f70,f119])).

fof(f126,plain,
    ( spl4_5
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f234,plain,
    ( sK2 = sK3
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f231,f71])).

fof(f231,plain,
    ( sK2 = sK3
    | ~ r2_xboole_0(sK2,sK3)
    | ~ spl4_5 ),
    inference(resolution,[],[f127,f81])).

fof(f81,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ r2_xboole_0(X2,X1) ) ),
    inference(resolution,[],[f61,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f127,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f222,plain,
    ( spl4_5
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f221,f215,f126])).

fof(f221,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f217,f106])).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK2)
      | r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f105,f45])).

fof(f217,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f215])).

fof(f166,plain,
    ( ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f164,f132])).

fof(f132,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f75,f121])).

fof(f164,plain,
    ( ~ m1_orders_2(sK2,sK0,sK2)
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f158,f132])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | ~ m1_orders_2(X0,sK0,sK2) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f78,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f47,f74,f70])).

fof(f47,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f48,f74,f70])).

fof(f48,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:27:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (1118)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.50  % (1110)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (1110)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (1129)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f289,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f77,f78,f166,f222,f235,f243,f245,f259,f270,f285])).
% 0.22/0.50  fof(f285,plain,(
% 0.22/0.50    ~spl4_1 | ~spl4_4),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f284])).
% 0.22/0.50  fof(f284,plain,(
% 0.22/0.50    $false | (~spl4_1 | ~spl4_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f274,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f63])).
% 0.22/0.51  % (1132)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (1131)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (1105)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.51    inference(flattening,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.51  fof(f274,plain,(
% 0.22/0.51    r2_xboole_0(sK2,sK2) | (~spl4_1 | ~spl4_4)),
% 0.22/0.51    inference(backward_demodulation,[],[f71,f121])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    sK2 = sK3 | ~spl4_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f119])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    spl4_4 <=> sK2 = sK3),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    r2_xboole_0(sK2,sK3) | ~spl4_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    spl4_1 <=> r2_xboole_0(sK2,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.51  fof(f270,plain,(
% 0.22/0.51    spl4_6 | spl4_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f265,f160,f157])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    spl4_6 <=> ! [X0] : (~m1_orders_2(X0,sK0,sK2) | ~m1_orders_2(sK2,sK0,X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    spl4_7 <=> k1_xboole_0 = sK2),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.51  fof(f265,plain,(
% 0.22/0.51    ( ! [X2] : (k1_xboole_0 = sK2 | ~m1_orders_2(X2,sK0,sK2) | ~m1_orders_2(sK2,sK0,X2)) )),
% 0.22/0.51    inference(resolution,[],[f45,f154])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | k1_xboole_0 = X0 | ~m1_orders_2(X1,sK0,X0) | ~m1_orders_2(X0,sK0,X1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f153,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f32,f31,f30,f29])).
% 0.22/0.51  % (1114)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  % (1112)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (1112)Refutation not found, incomplete strategy% (1112)------------------------------
% 0.22/0.51  % (1112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1120)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (1112)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (1112)Memory used [KB]: 10618
% 0.22/0.51  % (1112)Time elapsed: 0.093 s
% 0.22/0.51  % (1112)------------------------------
% 0.22/0.51  % (1112)------------------------------
% 0.22/0.52  % (1111)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (1125)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (1105)Refutation not found, incomplete strategy% (1105)------------------------------
% 0.22/0.52  % (1105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1105)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1105)Memory used [KB]: 10618
% 0.22/0.52  % (1105)Time elapsed: 0.104 s
% 0.22/0.52  % (1105)------------------------------
% 0.22/0.52  % (1105)------------------------------
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) => (? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) => ((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.22/0.52    inference(negated_conjecture,[],[f10])).
% 0.22/0.52  fof(f10,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_orders_2(X1,sK0,X0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f152,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    v3_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_orders_2(X1,sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f151,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    v4_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_orders_2(X1,sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f150,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    v5_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_orders_2(X1,sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f147,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    l1_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_orders_2(X1,sK0,X0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1)) )),
% 0.22/0.52    inference(resolution,[],[f145,f97])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m2_orders_2(X0,sK0,sK1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f96,f39])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f95,f40])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f94,f41])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f93,f42])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f92,f43])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(resolution,[],[f57,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_orders_2(X2,X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f55,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    m2_orders_2(sK2,sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f259,plain,(
% 0.22/0.52    ~spl4_7),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f258])).
% 0.22/0.52  fof(f258,plain,(
% 0.22/0.52    $false | ~spl4_7),
% 0.22/0.52    inference(subsumption_resolution,[],[f252,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.52    inference(equality_resolution,[],[f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.22/0.52  fof(f252,plain,(
% 0.22/0.52    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_7),
% 0.22/0.52    inference(backward_demodulation,[],[f146,f162])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    k1_xboole_0 = sK2 | ~spl4_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f160])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    ~r1_xboole_0(sK2,sK2)),
% 0.22/0.52    inference(resolution,[],[f144,f45])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(sK2,X0)) )),
% 0.22/0.52    inference(resolution,[],[f143,f45])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(X1,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f142,f39])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X1,X0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f141,f40])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X1,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f140,f41])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X1,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f139,f42])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X1,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f138,f43])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X1,X0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(resolution,[],[f51,f44])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~r1_xboole_0(X2,X3) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).
% 0.22/0.52  fof(f245,plain,(
% 0.22/0.52    spl4_4 | spl4_1 | ~spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f123,f74,f70,f119])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    spl4_2 <=> m1_orders_2(sK2,sK0,sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    sK2 = sK3 | (spl4_1 | ~spl4_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f112,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ~r2_xboole_0(sK2,sK3) | spl4_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f70])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    sK2 = sK3 | r2_xboole_0(sK2,sK3) | ~spl4_2),
% 0.22/0.52    inference(resolution,[],[f110,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    r1_tarski(sK2,sK3) | ~spl4_2),
% 0.22/0.52    inference(resolution,[],[f107,f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    m1_orders_2(sK2,sK0,sK3) | ~spl4_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f74])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    ( ! [X1] : (~m1_orders_2(X1,sK0,sK3) | r1_tarski(X1,sK3)) )),
% 0.22/0.52    inference(resolution,[],[f105,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    m2_orders_2(sK3,sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f104,f39])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f103,f40])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f102,f41])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f101,f42])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f100,f43])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(resolution,[],[f97,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).
% 0.22/0.52  fof(f243,plain,(
% 0.22/0.52    spl4_2 | spl4_10 | spl4_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f211,f119,f215,f74])).
% 0.22/0.52  fof(f215,plain,(
% 0.22/0.52    spl4_10 <=> m1_orders_2(sK3,sK0,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.52  fof(f211,plain,(
% 0.22/0.52    sK2 = sK3 | m1_orders_2(sK3,sK0,sK2) | m1_orders_2(sK2,sK0,sK3)),
% 0.22/0.52    inference(resolution,[],[f208,f46])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | m1_orders_2(sK2,sK0,X0)) )),
% 0.22/0.52    inference(resolution,[],[f205,f45])).
% 0.22/0.52  fof(f205,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m2_orders_2(X1,sK0,sK1) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f204,f39])).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X1,sK0,X0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f203,f40])).
% 0.22/0.52  fof(f203,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X1,sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f202,f41])).
% 0.22/0.52  fof(f202,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X1,sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f201,f42])).
% 0.22/0.52  fof(f201,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X1,sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f200,f43])).
% 0.22/0.52  fof(f200,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X1,sK0,X0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(resolution,[],[f53,f44])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | m1_orders_2(X2,X0,X3) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).
% 0.22/0.52  fof(f235,plain,(
% 0.22/0.52    spl4_4 | ~spl4_1 | ~spl4_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f234,f126,f70,f119])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    spl4_5 <=> r1_tarski(sK3,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.52  fof(f234,plain,(
% 0.22/0.52    sK2 = sK3 | (~spl4_1 | ~spl4_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f231,f71])).
% 0.22/0.52  fof(f231,plain,(
% 0.22/0.52    sK2 = sK3 | ~r2_xboole_0(sK2,sK3) | ~spl4_5),
% 0.22/0.52    inference(resolution,[],[f127,f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~r1_tarski(X1,X2) | X1 = X2 | ~r2_xboole_0(X2,X1)) )),
% 0.22/0.52    inference(resolution,[],[f61,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    r1_tarski(sK3,sK2) | ~spl4_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f126])).
% 0.22/0.52  fof(f222,plain,(
% 0.22/0.52    spl4_5 | ~spl4_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f221,f215,f126])).
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    r1_tarski(sK3,sK2) | ~spl4_10),
% 0.22/0.52    inference(resolution,[],[f217,f106])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | r1_tarski(X0,sK2)) )),
% 0.22/0.52    inference(resolution,[],[f105,f45])).
% 0.22/0.52  fof(f217,plain,(
% 0.22/0.52    m1_orders_2(sK3,sK0,sK2) | ~spl4_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f215])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    ~spl4_2 | ~spl4_4 | ~spl4_6),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f165])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    $false | (~spl4_2 | ~spl4_4 | ~spl4_6)),
% 0.22/0.52    inference(subsumption_resolution,[],[f164,f132])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    m1_orders_2(sK2,sK0,sK2) | (~spl4_2 | ~spl4_4)),
% 0.22/0.52    inference(backward_demodulation,[],[f75,f121])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    ~m1_orders_2(sK2,sK0,sK2) | (~spl4_2 | ~spl4_4 | ~spl4_6)),
% 0.22/0.52    inference(resolution,[],[f158,f132])).
% 0.22/0.52  fof(f158,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_orders_2(sK2,sK0,X0) | ~m1_orders_2(X0,sK0,sK2)) ) | ~spl4_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f157])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    spl4_1 | spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f47,f74,f70])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ~spl4_1 | ~spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f48,f74,f70])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (1110)------------------------------
% 0.22/0.52  % (1110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1110)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (1110)Memory used [KB]: 6268
% 0.22/0.52  % (1110)Time elapsed: 0.086 s
% 0.22/0.52  % (1110)------------------------------
% 0.22/0.52  % (1110)------------------------------
% 0.22/0.52  % (1104)Success in time 0.157 s
%------------------------------------------------------------------------------

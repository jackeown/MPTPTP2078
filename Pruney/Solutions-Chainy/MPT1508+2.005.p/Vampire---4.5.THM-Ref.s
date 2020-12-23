%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 668 expanded)
%              Number of leaves         :   15 ( 240 expanded)
%              Depth                    :   41
%              Number of atoms          :  584 (4713 expanded)
%              Number of equality atoms :   41 ( 592 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(subsumption_resolution,[],[f147,f51])).

fof(f51,plain,(
    r3_lattice3(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK4 != k16_lattice3(sK3,sK5)
    & r3_lattice3(sK3,sK4,sK5)
    & r2_hidden(sK4,sK5)
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l3_lattices(sK3)
    & v4_lattice3(sK3)
    & v10_lattices(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f14,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k16_lattice3(X0,X2) != X1
                & r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(sK3,X2) != X1
              & r3_lattice3(sK3,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l3_lattices(sK3)
      & v4_lattice3(sK3)
      & v10_lattices(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k16_lattice3(sK3,X2) != X1
            & r3_lattice3(sK3,X1,X2)
            & r2_hidden(X1,X2) )
        & m1_subset_1(X1,u1_struct_0(sK3)) )
   => ( ? [X2] :
          ( k16_lattice3(sK3,X2) != sK4
          & r3_lattice3(sK3,sK4,X2)
          & r2_hidden(sK4,X2) )
      & m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

% (8317)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (8309)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (8309)Refutation not found, incomplete strategy% (8309)------------------------------
% (8309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8309)Termination reason: Refutation not found, incomplete strategy

% (8309)Memory used [KB]: 10618
% (8309)Time elapsed: 0.092 s
% (8309)------------------------------
% (8309)------------------------------
% (8328)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (8310)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (8313)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% (8330)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% (8321)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% (8319)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% (8316)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f35,plain,
    ( ? [X2] :
        ( k16_lattice3(sK3,X2) != sK4
        & r3_lattice3(sK3,sK4,X2)
        & r2_hidden(sK4,X2) )
   => ( sK4 != k16_lattice3(sK3,sK5)
      & r3_lattice3(sK3,sK4,sK5)
      & r2_hidden(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( r3_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k16_lattice3(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k16_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).

fof(f147,plain,(
    ~ r3_lattice3(sK3,sK4,sK5) ),
    inference(subsumption_resolution,[],[f146,f52])).

fof(f52,plain,(
    sK4 != k16_lattice3(sK3,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f146,plain,
    ( sK4 = k16_lattice3(sK3,sK5)
    | ~ r3_lattice3(sK3,sK4,sK5) ),
    inference(resolution,[],[f145,f50])).

fof(f50,plain,(
    r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,X0)
      | sK4 = k16_lattice3(sK3,X0)
      | ~ r3_lattice3(sK3,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f144,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f144,plain,(
    ! [X0] :
      ( ~ r3_lattice3(sK3,sK4,X0)
      | sK4 = k16_lattice3(sK3,X0)
      | ~ r2_hidden(sK4,X0)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f143,f48])).

fof(f48,plain,(
    l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f143,plain,(
    ! [X0] :
      ( ~ r3_lattice3(sK3,sK4,X0)
      | sK4 = k16_lattice3(sK3,X0)
      | ~ r2_hidden(sK4,X0)
      | ~ l3_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f142,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f142,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
      | ~ r3_lattice3(sK3,sK4,X0)
      | sK4 = k16_lattice3(sK3,X0)
      | ~ r2_hidden(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f141,f45])).

fof(f141,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
      | ~ r3_lattice3(sK3,sK4,X0)
      | sK4 = k16_lattice3(sK3,X0)
      | ~ r2_hidden(sK4,X0)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f140,f46])).

fof(f46,plain,(
    v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f140,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
      | ~ r3_lattice3(sK3,sK4,X0)
      | sK4 = k16_lattice3(sK3,X0)
      | ~ r2_hidden(sK4,X0)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f139,f47])).

fof(f47,plain,(
    v4_lattice3(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f139,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
      | ~ r3_lattice3(sK3,sK4,X0)
      | sK4 = k16_lattice3(sK3,X0)
      | ~ r2_hidden(sK4,X0)
      | ~ v4_lattice3(sK3)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f138,f48])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
      | ~ r3_lattice3(sK3,sK4,X0)
      | sK4 = k16_lattice3(sK3,X0)
      | ~ r2_hidden(sK4,X0)
      | ~ l3_lattices(sK3)
      | ~ v4_lattice3(sK3)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f137,f49])).

fof(f49,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f137,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
      | ~ r3_lattice3(sK3,sK4,X0)
      | sK4 = k16_lattice3(sK3,X0)
      | ~ r2_hidden(sK4,X0)
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | ~ v4_lattice3(sK3)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f136,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

fof(f136,plain,(
    ! [X0] :
      ( ~ r3_lattices(sK3,k16_lattice3(sK3,X0),sK4)
      | ~ m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
      | ~ r3_lattice3(sK3,sK4,X0)
      | sK4 = k16_lattice3(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f135,f49])).

fof(f135,plain,(
    ! [X0] :
      ( sK4 = k16_lattice3(sK3,X0)
      | ~ m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
      | ~ r3_lattice3(sK3,sK4,X0)
      | ~ r3_lattices(sK3,k16_lattice3(sK3,X0),sK4)
      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f134,f117])).

fof(f117,plain,(
    ! [X2,X1] :
      ( r1_lattices(sK3,k16_lattice3(sK3,X2),X1)
      | ~ r3_lattices(sK3,k16_lattice3(sK3,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f116,f45])).

fof(f116,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ r3_lattices(sK3,k16_lattice3(sK3,X2),X1)
      | r1_lattices(sK3,k16_lattice3(sK3,X2),X1)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f114,f48])).

fof(f114,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ r3_lattices(sK3,k16_lattice3(sK3,X2),X1)
      | r1_lattices(sK3,k16_lattice3(sK3,X2),X1)
      | ~ l3_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f112,f71])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ r3_lattices(sK3,X0,X1)
      | r1_lattices(sK3,X0,X1) ) ),
    inference(subsumption_resolution,[],[f111,f45])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | r1_lattices(sK3,X0,X1)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f110,f80])).

fof(f80,plain,(
    v6_lattices(sK3) ),
    inference(resolution,[],[f77,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f77,plain,(
    sP0(sK3) ),
    inference(subsumption_resolution,[],[f76,f48])).

fof(f76,plain,
    ( sP0(sK3)
    | ~ l3_lattices(sK3) ),
    inference(subsumption_resolution,[],[f75,f45])).

fof(f75,plain,
    ( sP0(sK3)
    | v2_struct_0(sK3)
    | ~ l3_lattices(sK3) ),
    inference(resolution,[],[f59,f46])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | sP0(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f17,f28])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | r1_lattices(sK3,X0,X1)
      | ~ v6_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f109,f79])).

fof(f79,plain,(
    v8_lattices(sK3) ),
    inference(resolution,[],[f77,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | r1_lattices(sK3,X0,X1)
      | ~ v8_lattices(sK3)
      | ~ v6_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f108,f48])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | r1_lattices(sK3,X0,X1)
      | ~ v8_lattices(sK3)
      | ~ v6_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f72,f78])).

fof(f78,plain,(
    v9_lattices(sK3) ),
    inference(resolution,[],[f77,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f134,plain,(
    ! [X0] :
      ( ~ r1_lattices(sK3,k16_lattice3(sK3,X0),sK4)
      | sK4 = k16_lattice3(sK3,X0)
      | ~ m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
      | ~ r3_lattice3(sK3,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f133,f48])).

fof(f133,plain,(
    ! [X0] :
      ( sK4 = k16_lattice3(sK3,X0)
      | ~ r1_lattices(sK3,k16_lattice3(sK3,X0),sK4)
      | ~ m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
      | ~ r3_lattice3(sK3,sK4,X0)
      | ~ l3_lattices(sK3) ) ),
    inference(resolution,[],[f132,f53])).

fof(f53,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f132,plain,(
    ! [X0] :
      ( ~ l2_lattices(sK3)
      | sK4 = k16_lattice3(sK3,X0)
      | ~ r1_lattices(sK3,k16_lattice3(sK3,X0),sK4)
      | ~ m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
      | ~ r3_lattice3(sK3,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f131,f45])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r3_lattice3(sK3,sK4,X0)
      | sK4 = k16_lattice3(sK3,X0)
      | ~ r1_lattices(sK3,k16_lattice3(sK3,X0),sK4)
      | ~ m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
      | ~ l2_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f130,f81])).

fof(f81,plain,(
    v4_lattices(sK3) ),
    inference(resolution,[],[f77,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v4_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f130,plain,(
    ! [X0] :
      ( ~ r3_lattice3(sK3,sK4,X0)
      | sK4 = k16_lattice3(sK3,X0)
      | ~ r1_lattices(sK3,k16_lattice3(sK3,X0),sK4)
      | ~ m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
      | ~ l2_lattices(sK3)
      | ~ v4_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f129,f49])).

fof(f129,plain,(
    ! [X0] :
      ( ~ r3_lattice3(sK3,sK4,X0)
      | sK4 = k16_lattice3(sK3,X0)
      | ~ r1_lattices(sK3,k16_lattice3(sK3,X0),sK4)
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
      | ~ l2_lattices(sK3)
      | ~ v4_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f128,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,X1)
      | X1 = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

fof(f128,plain,(
    ! [X0] :
      ( r1_lattices(sK3,sK4,k16_lattice3(sK3,X0))
      | ~ r3_lattice3(sK3,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f127,f45])).

fof(f127,plain,(
    ! [X0] :
      ( r1_lattices(sK3,sK4,k16_lattice3(sK3,X0))
      | ~ r3_lattice3(sK3,sK4,X0)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f126,f48])).

fof(f126,plain,(
    ! [X0] :
      ( r1_lattices(sK3,sK4,k16_lattice3(sK3,X0))
      | ~ r3_lattice3(sK3,sK4,X0)
      | ~ l3_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f120,f71])).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
      | r1_lattices(sK3,sK4,k16_lattice3(sK3,X0))
      | ~ r3_lattice3(sK3,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f118,f49])).

fof(f118,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
      | r1_lattices(sK3,sK4,k16_lattice3(sK3,X0))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ r3_lattice3(sK3,sK4,X0) ) ),
    inference(resolution,[],[f113,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ r3_lattice3(sK3,X0,X1) ) ),
    inference(resolution,[],[f66,f92])).

fof(f92,plain,(
    ! [X0] : sP1(k16_lattice3(sK3,X0),sK3,X0) ),
    inference(resolution,[],[f90,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ sP2(X0,k16_lattice3(X0,X2))
      | sP1(k16_lattice3(X0,X2),X0,X2) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k16_lattice3(X0,X2) != X1
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k16_lattice3(X0,X2) = X1
            | ~ sP1(X1,X0,X2) )
          & ( sP1(X1,X0,X2)
            | k16_lattice3(X0,X2) != X1 ) )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k16_lattice3(X0,X2) = X1
        <=> sP1(X1,X0,X2) )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f90,plain,(
    ! [X0] : sP2(sK3,k16_lattice3(sK3,X0)) ),
    inference(subsumption_resolution,[],[f89,f45])).

fof(f89,plain,(
    ! [X0] :
      ( sP2(sK3,k16_lattice3(sK3,X0))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f87,f48])).

fof(f87,plain,(
    ! [X0] :
      ( sP2(sK3,k16_lattice3(sK3,X0))
      | ~ l3_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f85,f71])).

fof(f85,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f84,f45])).

fof(f84,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK3,X0)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f83,f46])).

fof(f83,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK3,X0)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f82,f48])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | sP2(sK3,X0)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f70,f47])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | sP2(X0,X1)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f23,f31,f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ( ! [X3] :
            ( r3_lattices(X0,X3,X1)
            | ~ r3_lattice3(X0,X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & r3_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r3_lattice3(X1,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r3_lattices(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ r3_lattices(X1,sK6(X0,X1,X2),X0)
          & r3_lattice3(X1,sK6(X0,X1,X2),X2)
          & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) )
        | ~ r3_lattice3(X1,X0,X2) )
      & ( ( ! [X4] :
              ( r3_lattices(X1,X4,X0)
              | ~ r3_lattice3(X1,X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r3_lattice3(X1,X0,X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X1,X3,X0)
          & r3_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r3_lattices(X1,sK6(X0,X1,X2),X0)
        & r3_lattice3(X1,sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ r3_lattices(X1,X3,X0)
            & r3_lattice3(X1,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ r3_lattice3(X1,X0,X2) )
      & ( ( ! [X4] :
              ( r3_lattices(X1,X4,X0)
              | ~ r3_lattice3(X1,X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r3_lattice3(X1,X0,X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ~ r3_lattices(X0,X3,X1)
            & r3_lattice3(X0,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( ! [X3] :
              ( r3_lattices(X0,X3,X1)
              | ~ r3_lattice3(X0,X3,X2)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r3_lattice3(X0,X1,X2) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ~ r3_lattices(X0,X3,X1)
            & r3_lattice3(X0,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( ! [X3] :
              ( r3_lattices(X0,X3,X1)
              | ~ r3_lattice3(X0,X3,X2)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r3_lattice3(X0,X1,X2) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f113,plain,(
    ! [X0] :
      ( ~ r3_lattices(sK3,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | r1_lattices(sK3,sK4,X0) ) ),
    inference(resolution,[],[f112,f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:50:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (8315)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.49  % (8323)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (8315)Refutation not found, incomplete strategy% (8315)------------------------------
% 0.22/0.50  % (8315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (8315)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (8315)Memory used [KB]: 10618
% 0.22/0.50  % (8315)Time elapsed: 0.080 s
% 0.22/0.50  % (8315)------------------------------
% 0.22/0.50  % (8315)------------------------------
% 0.22/0.50  % (8312)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (8329)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (8312)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f147,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    r3_lattice3(sK3,sK4,sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ((sK4 != k16_lattice3(sK3,sK5) & r3_lattice3(sK3,sK4,sK5) & r2_hidden(sK4,sK5)) & m1_subset_1(sK4,u1_struct_0(sK3))) & l3_lattices(sK3) & v4_lattice3(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f14,f35,f34,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK3,X2) != X1 & r3_lattice3(sK3,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK3))) & l3_lattices(sK3) & v4_lattice3(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : (k16_lattice3(sK3,X2) != X1 & r3_lattice3(sK3,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK3))) => (? [X2] : (k16_lattice3(sK3,X2) != sK4 & r3_lattice3(sK3,sK4,X2) & r2_hidden(sK4,X2)) & m1_subset_1(sK4,u1_struct_0(sK3)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  % (8317)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (8309)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (8309)Refutation not found, incomplete strategy% (8309)------------------------------
% 0.22/0.51  % (8309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8309)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8309)Memory used [KB]: 10618
% 0.22/0.51  % (8309)Time elapsed: 0.092 s
% 0.22/0.51  % (8309)------------------------------
% 0.22/0.51  % (8309)------------------------------
% 0.22/0.51  % (8328)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (8310)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (8313)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (8330)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (8321)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (8319)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (8316)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ? [X2] : (k16_lattice3(sK3,X2) != sK4 & r3_lattice3(sK3,sK4,X2) & r2_hidden(sK4,X2)) => (sK4 != k16_lattice3(sK3,sK5) & r3_lattice3(sK3,sK4,sK5) & r2_hidden(sK4,sK5))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.22/0.52    inference(negated_conjecture,[],[f8])).
% 0.22/0.52  fof(f8,conjecture,(
% 0.22/0.52    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    ~r3_lattice3(sK3,sK4,sK5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f146,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    sK4 != k16_lattice3(sK3,sK5)),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    sK4 = k16_lattice3(sK3,sK5) | ~r3_lattice3(sK3,sK4,sK5)),
% 0.22/0.52    inference(resolution,[],[f145,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    r2_hidden(sK4,sK5)),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(sK4,X0) | sK4 = k16_lattice3(sK3,X0) | ~r3_lattice3(sK3,sK4,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f144,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ~v2_struct_0(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    ( ! [X0] : (~r3_lattice3(sK3,sK4,X0) | sK4 = k16_lattice3(sK3,X0) | ~r2_hidden(sK4,X0) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f143,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    l3_lattices(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    ( ! [X0] : (~r3_lattice3(sK3,sK4,X0) | sK4 = k16_lattice3(sK3,X0) | ~r2_hidden(sK4,X0) | ~l3_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(resolution,[],[f142,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) | ~r3_lattice3(sK3,sK4,X0) | sK4 = k16_lattice3(sK3,X0) | ~r2_hidden(sK4,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f141,f45])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) | ~r3_lattice3(sK3,sK4,X0) | sK4 = k16_lattice3(sK3,X0) | ~r2_hidden(sK4,X0) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f140,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    v10_lattices(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) | ~r3_lattice3(sK3,sK4,X0) | sK4 = k16_lattice3(sK3,X0) | ~r2_hidden(sK4,X0) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f139,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    v4_lattice3(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) | ~r3_lattice3(sK3,sK4,X0) | sK4 = k16_lattice3(sK3,X0) | ~r2_hidden(sK4,X0) | ~v4_lattice3(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f138,f48])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) | ~r3_lattice3(sK3,sK4,X0) | sK4 = k16_lattice3(sK3,X0) | ~r2_hidden(sK4,X0) | ~l3_lattices(sK3) | ~v4_lattice3(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f137,f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) | ~r3_lattice3(sK3,sK4,X0) | sK4 = k16_lattice3(sK3,X0) | ~r2_hidden(sK4,X0) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l3_lattices(sK3) | ~v4_lattice3(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(resolution,[],[f136,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    ( ! [X0] : (~r3_lattices(sK3,k16_lattice3(sK3,X0),sK4) | ~m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) | ~r3_lattice3(sK3,sK4,X0) | sK4 = k16_lattice3(sK3,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f135,f49])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    ( ! [X0] : (sK4 = k16_lattice3(sK3,X0) | ~m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) | ~r3_lattice3(sK3,sK4,X0) | ~r3_lattices(sK3,k16_lattice3(sK3,X0),sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3))) )),
% 0.22/0.52    inference(resolution,[],[f134,f117])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    ( ! [X2,X1] : (r1_lattices(sK3,k16_lattice3(sK3,X2),X1) | ~r3_lattices(sK3,k16_lattice3(sK3,X2),X1) | ~m1_subset_1(X1,u1_struct_0(sK3))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f116,f45])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | ~r3_lattices(sK3,k16_lattice3(sK3,X2),X1) | r1_lattices(sK3,k16_lattice3(sK3,X2),X1) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f114,f48])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | ~r3_lattices(sK3,k16_lattice3(sK3,X2),X1) | r1_lattices(sK3,k16_lattice3(sK3,X2),X1) | ~l3_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(resolution,[],[f112,f71])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r3_lattices(sK3,X0,X1) | r1_lattices(sK3,X0,X1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f111,f45])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r3_lattices(sK3,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | r1_lattices(sK3,X0,X1) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f110,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    v6_lattices(sK3)),
% 0.22/0.52    inference(resolution,[],[f77,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0] : (~sP0(X0) | v6_lattices(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    sP0(sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f76,f48])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    sP0(sK3) | ~l3_lattices(sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f75,f45])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    sP0(sK3) | v2_struct_0(sK3) | ~l3_lattices(sK3)),
% 0.22/0.52    inference(resolution,[],[f59,f46])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X0] : (~v10_lattices(X0) | sP0(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.22/0.52    inference(definition_folding,[],[f17,f28])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.22/0.52    inference(flattening,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r3_lattices(sK3,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | r1_lattices(sK3,X0,X1) | ~v6_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f109,f79])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    v8_lattices(sK3)),
% 0.22/0.52    inference(resolution,[],[f77,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0] : (~sP0(X0) | v8_lattices(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r3_lattices(sK3,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | r1_lattices(sK3,X0,X1) | ~v8_lattices(sK3) | ~v6_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f108,f48])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r3_lattices(sK3,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~l3_lattices(sK3) | r1_lattices(sK3,X0,X1) | ~v8_lattices(sK3) | ~v6_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(resolution,[],[f72,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    v9_lattices(sK3)),
% 0.22/0.52    inference(resolution,[],[f77,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0] : (~sP0(X0) | v9_lattices(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_lattices(sK3,k16_lattice3(sK3,X0),sK4) | sK4 = k16_lattice3(sK3,X0) | ~m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) | ~r3_lattice3(sK3,sK4,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f133,f48])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    ( ! [X0] : (sK4 = k16_lattice3(sK3,X0) | ~r1_lattices(sK3,k16_lattice3(sK3,X0),sK4) | ~m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) | ~r3_lattice3(sK3,sK4,X0) | ~l3_lattices(sK3)) )),
% 0.22/0.52    inference(resolution,[],[f132,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    ( ! [X0] : (~l2_lattices(sK3) | sK4 = k16_lattice3(sK3,X0) | ~r1_lattices(sK3,k16_lattice3(sK3,X0),sK4) | ~m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) | ~r3_lattice3(sK3,sK4,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f131,f45])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    ( ! [X0] : (~r3_lattice3(sK3,sK4,X0) | sK4 = k16_lattice3(sK3,X0) | ~r1_lattices(sK3,k16_lattice3(sK3,X0),sK4) | ~m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) | ~l2_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f130,f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    v4_lattices(sK3)),
% 0.22/0.52    inference(resolution,[],[f77,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0] : (~sP0(X0) | v4_lattices(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    ( ! [X0] : (~r3_lattice3(sK3,sK4,X0) | sK4 = k16_lattice3(sK3,X0) | ~r1_lattices(sK3,k16_lattice3(sK3,X0),sK4) | ~m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) | ~l2_lattices(sK3) | ~v4_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f129,f49])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    ( ! [X0] : (~r3_lattice3(sK3,sK4,X0) | sK4 = k16_lattice3(sK3,X0) | ~r1_lattices(sK3,k16_lattice3(sK3,X0),sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) | ~l2_lattices(sK3) | ~v4_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(resolution,[],[f128,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_lattices(X0,X2,X1) | X1 = X2 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : ((l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_lattices(X0,X2,X1) & r1_lattices(X0,X1,X2)) => X1 = X2))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    ( ! [X0] : (r1_lattices(sK3,sK4,k16_lattice3(sK3,X0)) | ~r3_lattice3(sK3,sK4,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f127,f45])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ( ! [X0] : (r1_lattices(sK3,sK4,k16_lattice3(sK3,X0)) | ~r3_lattice3(sK3,sK4,X0) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f126,f48])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    ( ! [X0] : (r1_lattices(sK3,sK4,k16_lattice3(sK3,X0)) | ~r3_lattice3(sK3,sK4,X0) | ~l3_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(resolution,[],[f120,f71])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) | r1_lattices(sK3,sK4,k16_lattice3(sK3,X0)) | ~r3_lattice3(sK3,sK4,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f118,f49])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) | r1_lattices(sK3,sK4,k16_lattice3(sK3,X0)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r3_lattice3(sK3,sK4,X0)) )),
% 0.22/0.52    inference(resolution,[],[f113,f97])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r3_lattices(sK3,X0,k16_lattice3(sK3,X1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r3_lattice3(sK3,X0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f66,f92])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ( ! [X0] : (sP1(k16_lattice3(sK3,X0),sK3,X0)) )),
% 0.22/0.52    inference(resolution,[],[f90,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    ( ! [X2,X0] : (~sP2(X0,k16_lattice3(X0,X2)) | sP1(k16_lattice3(X0,X2),X0,X2)) )),
% 0.22/0.52    inference(equality_resolution,[],[f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k16_lattice3(X0,X2) != X1 | ~sP2(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k16_lattice3(X0,X2) != X1)) | ~sP2(X0,X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> sP1(X1,X0,X2)) | ~sP2(X0,X1))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ( ! [X0] : (sP2(sK3,k16_lattice3(sK3,X0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f89,f45])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ( ! [X0] : (sP2(sK3,k16_lattice3(sK3,X0)) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f87,f48])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ( ! [X0] : (sP2(sK3,k16_lattice3(sK3,X0)) | ~l3_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(resolution,[],[f85,f71])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | sP2(sK3,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f84,f45])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | sP2(sK3,X0) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f83,f46])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | sP2(sK3,X0) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f82,f48])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~l3_lattices(sK3) | sP2(sK3,X0) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.52    inference(resolution,[],[f70,f47])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v4_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | sP2(X0,X1) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (sP2(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(definition_folding,[],[f23,f31,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r3_lattices(X1,X4,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (~r3_lattices(X1,sK6(X0,X1,X2),X0) & r3_lattice3(X1,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))) | ~r3_lattice3(X1,X0,X2)) & ((! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & r3_lattice3(X1,X0,X2)) | ~sP1(X0,X1,X2)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r3_lattices(X1,sK6(X0,X1,X2),X0) & r3_lattice3(X1,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) | ~r3_lattice3(X1,X0,X2)) & ((! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & r3_lattice3(X1,X0,X2)) | ~sP1(X0,X1,X2)))),
% 0.22/0.52    inference(rectify,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | ~sP1(X1,X0,X2)))),
% 0.22/0.52    inference(flattening,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | ~sP1(X1,X0,X2)))),
% 0.22/0.52    inference(nnf_transformation,[],[f30])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ( ! [X0] : (~r3_lattices(sK3,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | r1_lattices(sK3,sK4,X0)) )),
% 0.22/0.52    inference(resolution,[],[f112,f49])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (8312)------------------------------
% 0.22/0.52  % (8312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8312)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (8312)Memory used [KB]: 6268
% 0.22/0.52  % (8312)Time elapsed: 0.099 s
% 0.22/0.52  % (8312)------------------------------
% 0.22/0.52  % (8312)------------------------------
% 0.22/0.52  % (8308)Success in time 0.159 s
%------------------------------------------------------------------------------

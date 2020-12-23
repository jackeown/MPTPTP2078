%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 207 expanded)
%              Number of leaves         :   18 (  68 expanded)
%              Depth                    :   27
%              Number of atoms          :  526 (1282 expanded)
%              Number of equality atoms :   48 ( 167 expanded)
%              Maximal formula depth    :   15 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f216,plain,(
    $false ),
    inference(subsumption_resolution,[],[f215,f52])).

fof(f52,plain,(
    m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK7 != k16_lattice3(sK6,sK8)
    & r3_lattice3(sK6,sK7,sK8)
    & r2_hidden(sK7,sK8)
    & m1_subset_1(sK7,u1_struct_0(sK6))
    & l3_lattices(sK6)
    & v4_lattice3(sK6)
    & v10_lattices(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f9,f31,f30,f29])).

fof(f29,plain,
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
              ( k16_lattice3(sK6,X2) != X1
              & r3_lattice3(sK6,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK6)) )
      & l3_lattices(sK6)
      & v4_lattice3(sK6)
      & v10_lattices(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k16_lattice3(sK6,X2) != X1
            & r3_lattice3(sK6,X1,X2)
            & r2_hidden(X1,X2) )
        & m1_subset_1(X1,u1_struct_0(sK6)) )
   => ( ? [X2] :
          ( k16_lattice3(sK6,X2) != sK7
          & r3_lattice3(sK6,sK7,X2)
          & r2_hidden(sK7,X2) )
      & m1_subset_1(sK7,u1_struct_0(sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( k16_lattice3(sK6,X2) != sK7
        & r3_lattice3(sK6,sK7,X2)
        & r2_hidden(sK7,X2) )
   => ( sK7 != k16_lattice3(sK6,sK8)
      & r3_lattice3(sK6,sK7,sK8)
      & r2_hidden(sK7,sK8) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f215,plain,(
    ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f214,f53])).

fof(f53,plain,(
    r2_hidden(sK7,sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f214,plain,
    ( ~ r2_hidden(sK7,sK8)
    | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(trivial_inequality_removal,[],[f210])).

fof(f210,plain,
    ( sK7 != sK7
    | ~ r2_hidden(sK7,sK8)
    | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(resolution,[],[f199,f54])).

fof(f54,plain,(
    r3_lattice3(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f199,plain,(
    ! [X0] :
      ( ~ r3_lattice3(sK6,X0,sK8)
      | sK7 != X0
      | ~ r2_hidden(X0,sK8)
      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f198,f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( sP4(X0,X1,X3)
      | ~ r3_lattice3(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2)
      | ~ r3_lattice3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r3_lattice3(X1,sK11(X0,X1,X2),X0)
          & sK11(X0,X1,X2) = X2
          & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK11(X0,X1,X2),X0)
        & sK11(X0,X1,X2) = X2
        & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r3_lattice3(X1,X4,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ( sP4(X2,X1,X0)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP4(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( sP4(X2,X1,X0)
    <=> ? [X3] :
          ( r3_lattice3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f198,plain,(
    ! [X0] :
      ( ~ sP4(sK8,sK6,X0)
      | ~ r2_hidden(X0,sK8)
      | sK7 != X0 ) ),
    inference(subsumption_resolution,[],[f197,f49])).

fof(f49,plain,(
    v10_lattices(sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f197,plain,(
    ! [X0] :
      ( sK7 != X0
      | ~ r2_hidden(X0,sK8)
      | ~ v10_lattices(sK6)
      | ~ sP4(sK8,sK6,X0) ) ),
    inference(subsumption_resolution,[],[f196,f50])).

fof(f50,plain,(
    v4_lattice3(sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f196,plain,(
    ! [X0] :
      ( sK7 != X0
      | ~ r2_hidden(X0,sK8)
      | ~ v4_lattice3(sK6)
      | ~ v10_lattices(sK6)
      | ~ sP4(sK8,sK6,X0) ) ),
    inference(subsumption_resolution,[],[f195,f51])).

fof(f51,plain,(
    l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f195,plain,(
    ! [X0] :
      ( sK7 != X0
      | ~ l3_lattices(sK6)
      | ~ r2_hidden(X0,sK8)
      | ~ v4_lattice3(sK6)
      | ~ v10_lattices(sK6)
      | ~ sP4(sK8,sK6,X0) ) ),
    inference(subsumption_resolution,[],[f193,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f193,plain,(
    ! [X0] :
      ( sK7 != X0
      | v2_struct_0(sK6)
      | ~ l3_lattices(sK6)
      | ~ r2_hidden(X0,sK8)
      | ~ v4_lattice3(sK6)
      | ~ v10_lattices(sK6)
      | ~ sP4(sK8,sK6,X0) ) ),
    inference(superposition,[],[f55,f187])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ r2_hidden(X1,X2)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | ~ sP4(X2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f186,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sP5(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( sP5(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f19,f27,f26])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> sP4(X2,X1,X0) )
      | ~ sP5(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | k16_lattice3(X0,X2) = X1
      | ~ r2_hidden(X1,X2)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | ~ sP4(X2,X0,X1)
      | ~ sP5(X1,X0,X2) ) ),
    inference(subsumption_resolution,[],[f183,f97])).

% (19546)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (19551)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (19527)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (19543)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% (19529)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% (19544)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (19534)Termination reason: Refutation not found, incomplete strategy

% (19534)Memory used [KB]: 1663
% (19534)Time elapsed: 0.126 s
% (19534)------------------------------
% (19534)------------------------------
% (19527)Refutation not found, incomplete strategy% (19527)------------------------------
% (19527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19527)Termination reason: Refutation not found, incomplete strategy

% (19527)Memory used [KB]: 10618
% (19527)Time elapsed: 0.138 s
% (19527)------------------------------
% (19527)------------------------------
% (19540)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (19538)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (19537)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% (19552)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (19549)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (19550)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% (19547)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (19528)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X1))
      | ~ sP4(X0,X1,X2)
      | ~ sP4(X0,X1,X2) ) ),
    inference(superposition,[],[f74,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sK11(X0,X1,X2) = X2
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k16_lattice3(X0,X2) = X1
      | ~ r2_hidden(X1,X2)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | ~ sP4(X2,X0,X1)
      | ~ sP5(X1,X0,X2) ) ),
    inference(resolution,[],[f156,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ sP4(X2,X1,X0)
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ~ sP4(X2,X1,X0) )
        & ( sP4(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(X2,X1))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | k16_lattice3(X2,X1) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2) ) ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | k16_lattice3(X2,X1) = X0
      | ~ r2_hidden(X0,a_2_1_lattice3(X2,X1))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2) ) ),
    inference(resolution,[],[f153,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_lattice3(X0,X2,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | k16_lattice3(X0,X1) = X2
      | ~ r2_hidden(X2,a_2_1_lattice3(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X1) = X2
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ r4_lattice3(X0,X2,a_2_1_lattice3(X0,X1))
      | ~ r2_hidden(X2,a_2_1_lattice3(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f57,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X2) = X1
      | ~ r4_lattice3(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k15_lattice3(X0,X2) = X1
              | ~ r4_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k15_lattice3(X0,X2) = X1
              | ~ r4_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k15_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d22_lattice3)).

fof(f153,plain,(
    ! [X6,X4,X5] :
      ( r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6))
      | ~ r2_hidden(X4,X6)
      | ~ l3_lattices(X5)
      | v2_struct_0(X5)
      | ~ m1_subset_1(X4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f152,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP1(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f15,f21,f20])).

fof(f20,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X3,X1)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r4_lattice3(X0,X1,X2)
        <=> sP0(X1,X0,X2) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

fof(f152,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ r2_hidden(X4,X6)
      | ~ l3_lattices(X5)
      | v2_struct_0(X5)
      | r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6))
      | ~ sP1(X5,X4) ) ),
    inference(resolution,[],[f150,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | r4_lattice3(X0,X1,X2)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X0,X1,X2)
            | ~ sP0(X1,X0,X2) )
          & ( sP0(X1,X0,X2)
            | ~ r4_lattice3(X0,X1,X2) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f149,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,sK9(X1,X0,X2))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | sP0(X1,X0,X2) ) ),
    inference(resolution,[],[f71,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r1_lattices(X1,sK9(X0,X1,X2),X0)
          & r2_hidden(sK9(X0,X1,X2),X2)
          & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,sK9(X0,X1,X2),X0)
        & r2_hidden(sK9(X0,X1,X2),X2)
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X3,X0)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X3,X1)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X3,X1)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP3(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f24,f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( sP2(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP2(X1,X0,X2) )
      | ~ sP3(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ sP3(X2,sK9(X0,X2,a_2_1_lattice3(X2,X1)))
      | sP0(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ sP3(X2,sK9(X0,X2,a_2_1_lattice3(X2,X1)))
      | sP0(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | sP0(X0,X2,a_2_1_lattice3(X2,X1)) ) ),
    inference(resolution,[],[f120,f129])).

fof(f129,plain,(
    ! [X10,X8,X11,X9] :
      ( r3_lattice3(X10,sK9(X8,X9,a_2_1_lattice3(X10,X11)),X11)
      | ~ l3_lattices(X10)
      | v2_struct_0(X10)
      | sP0(X8,X9,a_2_1_lattice3(X10,X11)) ) ),
    inference(resolution,[],[f126,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | r3_lattice3(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,X2,X0)
      | ~ sP4(X0,X1,X2)
      | ~ sP4(X0,X1,X2) ) ),
    inference(superposition,[],[f76,f75])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK11(X0,X1,X2),X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,sK9(X2,X3,a_2_1_lattice3(X1,X0)))
      | sP0(X2,X3,a_2_1_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f102,f78])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(sK9(X2,X3,a_2_1_lattice3(X1,X0)),X1,X0)
      | sP4(X0,X1,sK9(X2,X3,a_2_1_lattice3(X1,X0)))
      | sP0(X2,X3,a_2_1_lattice3(X1,X0)) ) ),
    inference(resolution,[],[f72,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | sP4(X2,X1,X0)
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_lattice3(X1,sK9(X0,X1,X3),X2)
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ sP3(X1,sK9(X0,X1,X3))
      | sP0(X0,X1,X3) ) ),
    inference(resolution,[],[f113,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,sK9(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X2,X3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ r3_lattice3(X2,X3,X1)
      | ~ sP3(X2,X3) ) ),
    inference(resolution,[],[f67,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP2(X1,X0,X2) )
          & ( sP2(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP3(X0,X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK10(X0,X1,X2))
          & r2_hidden(sK10(X0,X1,X2),X2)
          & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK10(X0,X1,X2))
        & r2_hidden(sK10(X0,X1,X2),X2)
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X1,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X1,X3)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f55,plain,(
    sK7 != k16_lattice3(sK6,sK8) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:00:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (19530)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.56  % (19548)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.56  % (19531)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.56  % (19534)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.56  % (19534)Refutation not found, incomplete strategy% (19534)------------------------------
% 0.22/0.56  % (19534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (19542)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.56  % (19532)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.56  % (19533)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.56  % (19531)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (19539)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.57  % (19541)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f216,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(subsumption_resolution,[],[f215,f52])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    m1_subset_1(sK7,u1_struct_0(sK6))),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ((sK7 != k16_lattice3(sK6,sK8) & r3_lattice3(sK6,sK7,sK8) & r2_hidden(sK7,sK8)) & m1_subset_1(sK7,u1_struct_0(sK6))) & l3_lattices(sK6) & v4_lattice3(sK6) & v10_lattices(sK6) & ~v2_struct_0(sK6)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f9,f31,f30,f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK6,X2) != X1 & r3_lattice3(sK6,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK6))) & l3_lattices(sK6) & v4_lattice3(sK6) & v10_lattices(sK6) & ~v2_struct_0(sK6))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ? [X1] : (? [X2] : (k16_lattice3(sK6,X2) != X1 & r3_lattice3(sK6,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK6))) => (? [X2] : (k16_lattice3(sK6,X2) != sK7 & r3_lattice3(sK6,sK7,X2) & r2_hidden(sK7,X2)) & m1_subset_1(sK7,u1_struct_0(sK6)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ? [X2] : (k16_lattice3(sK6,X2) != sK7 & r3_lattice3(sK6,sK7,X2) & r2_hidden(sK7,X2)) => (sK7 != k16_lattice3(sK6,sK8) & r3_lattice3(sK6,sK7,sK8) & r2_hidden(sK7,sK8))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f9,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f8])).
% 0.22/0.57  fof(f8,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,negated_conjecture,(
% 0.22/0.57    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.22/0.57    inference(negated_conjecture,[],[f6])).
% 0.22/0.57  fof(f6,conjecture,(
% 0.22/0.57    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).
% 0.22/0.57  fof(f215,plain,(
% 0.22/0.57    ~m1_subset_1(sK7,u1_struct_0(sK6))),
% 0.22/0.57    inference(subsumption_resolution,[],[f214,f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    r2_hidden(sK7,sK8)),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f214,plain,(
% 0.22/0.57    ~r2_hidden(sK7,sK8) | ~m1_subset_1(sK7,u1_struct_0(sK6))),
% 0.22/0.57    inference(trivial_inequality_removal,[],[f210])).
% 0.22/0.57  fof(f210,plain,(
% 0.22/0.57    sK7 != sK7 | ~r2_hidden(sK7,sK8) | ~m1_subset_1(sK7,u1_struct_0(sK6))),
% 0.22/0.57    inference(resolution,[],[f199,f54])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    r3_lattice3(sK6,sK7,sK8)),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f199,plain,(
% 0.22/0.57    ( ! [X0] : (~r3_lattice3(sK6,X0,sK8) | sK7 != X0 | ~r2_hidden(X0,sK8) | ~m1_subset_1(X0,u1_struct_0(sK6))) )),
% 0.22/0.57    inference(resolution,[],[f198,f79])).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    ( ! [X0,X3,X1] : (sP4(X0,X1,X3) | ~r3_lattice3(X1,X3,X0) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.22/0.57    inference(equality_resolution,[],[f77])).
% 0.22/0.57  fof(f77,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2) | ~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK11(X0,X1,X2),X0) & sK11(X0,X1,X2) = X2 & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f45,f46])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK11(X0,X1,X2),X0) & sK11(X0,X1,X2) = X2 & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 0.22/0.57    inference(rectify,[],[f44])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ! [X2,X1,X0] : ((sP4(X2,X1,X0) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP4(X2,X1,X0)))),
% 0.22/0.57    inference(nnf_transformation,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X2,X1,X0] : (sP4(X2,X1,X0) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.22/0.57  fof(f198,plain,(
% 0.22/0.57    ( ! [X0] : (~sP4(sK8,sK6,X0) | ~r2_hidden(X0,sK8) | sK7 != X0) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f197,f49])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    v10_lattices(sK6)),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f197,plain,(
% 0.22/0.57    ( ! [X0] : (sK7 != X0 | ~r2_hidden(X0,sK8) | ~v10_lattices(sK6) | ~sP4(sK8,sK6,X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f196,f50])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    v4_lattice3(sK6)),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f196,plain,(
% 0.22/0.57    ( ! [X0] : (sK7 != X0 | ~r2_hidden(X0,sK8) | ~v4_lattice3(sK6) | ~v10_lattices(sK6) | ~sP4(sK8,sK6,X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f195,f51])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    l3_lattices(sK6)),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f195,plain,(
% 0.22/0.57    ( ! [X0] : (sK7 != X0 | ~l3_lattices(sK6) | ~r2_hidden(X0,sK8) | ~v4_lattice3(sK6) | ~v10_lattices(sK6) | ~sP4(sK8,sK6,X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f193,f48])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    ~v2_struct_0(sK6)),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f193,plain,(
% 0.22/0.57    ( ! [X0] : (sK7 != X0 | v2_struct_0(sK6) | ~l3_lattices(sK6) | ~r2_hidden(X0,sK8) | ~v4_lattice3(sK6) | ~v10_lattices(sK6) | ~sP4(sK8,sK6,X0)) )),
% 0.22/0.57    inference(superposition,[],[f55,f187])).
% 0.22/0.57  fof(f187,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | v2_struct_0(X0) | ~l3_lattices(X0) | ~r2_hidden(X1,X2) | ~v4_lattice3(X0) | ~v10_lattices(X0) | ~sP4(X2,X0,X1)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f186,f78])).
% 0.22/0.57  fof(f78,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (sP5(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (sP5(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 0.22/0.57    inference(definition_folding,[],[f19,f27,f26])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> sP4(X2,X1,X0)) | ~sP5(X0,X1,X2))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 0.22/0.57    inference(flattening,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).
% 0.22/0.57  fof(f186,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~l3_lattices(X0) | v2_struct_0(X0) | k16_lattice3(X0,X2) = X1 | ~r2_hidden(X1,X2) | ~v4_lattice3(X0) | ~v10_lattices(X0) | ~sP4(X2,X0,X1) | ~sP5(X1,X0,X2)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f183,f97])).
% 0.22/0.57  % (19546)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.57  % (19551)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.57  % (19527)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.57  % (19543)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.57  % (19529)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.57  % (19544)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.57  % (19534)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (19534)Memory used [KB]: 1663
% 0.22/0.57  % (19534)Time elapsed: 0.126 s
% 0.22/0.57  % (19534)------------------------------
% 0.22/0.57  % (19534)------------------------------
% 0.22/0.57  % (19527)Refutation not found, incomplete strategy% (19527)------------------------------
% 0.22/0.57  % (19527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (19527)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (19527)Memory used [KB]: 10618
% 0.22/0.57  % (19527)Time elapsed: 0.138 s
% 0.22/0.57  % (19527)------------------------------
% 0.22/0.57  % (19527)------------------------------
% 0.22/0.57  % (19540)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % (19538)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.67/0.58  % (19537)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.67/0.58  % (19552)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.67/0.58  % (19549)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.67/0.58  % (19550)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.67/0.58  % (19547)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.67/0.58  % (19528)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.67/0.59  fof(f97,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | m1_subset_1(X2,u1_struct_0(X1))) )),
% 1.67/0.59    inference(duplicate_literal_removal,[],[f96])).
% 1.67/0.59  fof(f96,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X1)) | ~sP4(X0,X1,X2) | ~sP4(X0,X1,X2)) )),
% 1.67/0.59    inference(superposition,[],[f74,f75])).
% 1.67/0.59  fof(f75,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (sK11(X0,X1,X2) = X2 | ~sP4(X0,X1,X2)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f47])).
% 1.67/0.59  fof(f74,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) | ~sP4(X0,X1,X2)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f47])).
% 1.67/0.59  fof(f183,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k16_lattice3(X0,X2) = X1 | ~r2_hidden(X1,X2) | ~v4_lattice3(X0) | ~v10_lattices(X0) | ~sP4(X2,X0,X1) | ~sP5(X1,X0,X2)) )),
% 1.67/0.59    inference(resolution,[],[f156,f73])).
% 1.67/0.59  fof(f73,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP4(X2,X1,X0) | ~sP5(X0,X1,X2)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f43])).
% 1.67/0.59  fof(f43,plain,(
% 1.67/0.59    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP4(X2,X1,X0)) & (sP4(X2,X1,X0) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~sP5(X0,X1,X2))),
% 1.67/0.59    inference(nnf_transformation,[],[f27])).
% 1.67/0.59  fof(f156,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_lattice3(X2,X1)) | ~l3_lattices(X2) | v2_struct_0(X2) | ~m1_subset_1(X0,u1_struct_0(X2)) | k16_lattice3(X2,X1) = X0 | ~r2_hidden(X0,X1) | ~v4_lattice3(X2) | ~v10_lattices(X2)) )),
% 1.67/0.59    inference(duplicate_literal_removal,[],[f154])).
% 1.67/0.59  fof(f154,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~l3_lattices(X2) | v2_struct_0(X2) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~l3_lattices(X2) | v2_struct_0(X2) | k16_lattice3(X2,X1) = X0 | ~r2_hidden(X0,a_2_1_lattice3(X2,X1)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~v4_lattice3(X2) | ~v10_lattices(X2)) )),
% 1.67/0.59    inference(resolution,[],[f153,f117])).
% 1.67/0.59  fof(f117,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~r4_lattice3(X0,X2,a_2_1_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0) | k16_lattice3(X0,X1) = X2 | ~r2_hidden(X2,a_2_1_lattice3(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~v10_lattices(X0)) )),
% 1.67/0.59    inference(duplicate_literal_removal,[],[f116])).
% 1.67/0.59  fof(f116,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (k16_lattice3(X0,X1) = X2 | ~l3_lattices(X0) | v2_struct_0(X0) | ~r4_lattice3(X0,X2,a_2_1_lattice3(X0,X1)) | ~r2_hidden(X2,a_2_1_lattice3(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.67/0.59    inference(superposition,[],[f57,f56])).
% 1.67/0.59  fof(f56,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (k15_lattice3(X0,X2) = X1 | ~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f11])).
% 1.67/0.59  fof(f11,plain,(
% 1.67/0.59    ! [X0] : (! [X1] : (! [X2] : (k15_lattice3(X0,X2) = X1 | ~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.67/0.59    inference(flattening,[],[f10])).
% 1.67/0.59  fof(f10,plain,(
% 1.67/0.59    ! [X0] : (! [X1] : (! [X2] : (k15_lattice3(X0,X2) = X1 | (~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.67/0.59    inference(ennf_transformation,[],[f5])).
% 1.67/0.59  fof(f5,axiom,(
% 1.67/0.59    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k15_lattice3(X0,X2) = X1)))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).
% 1.67/0.59  fof(f57,plain,(
% 1.67/0.59    ( ! [X0,X1] : (k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f13])).
% 1.67/0.59  fof(f13,plain,(
% 1.67/0.59    ! [X0] : (! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.67/0.59    inference(flattening,[],[f12])).
% 1.67/0.59  fof(f12,plain,(
% 1.67/0.59    ! [X0] : (! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.67/0.59    inference(ennf_transformation,[],[f3])).
% 1.67/0.59  fof(f3,axiom,(
% 1.67/0.59    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d22_lattice3)).
% 1.67/0.59  fof(f153,plain,(
% 1.67/0.59    ( ! [X6,X4,X5] : (r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6)) | ~r2_hidden(X4,X6) | ~l3_lattices(X5) | v2_struct_0(X5) | ~m1_subset_1(X4,u1_struct_0(X5))) )),
% 1.67/0.59    inference(subsumption_resolution,[],[f152,f64])).
% 1.67/0.59  fof(f64,plain,(
% 1.67/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP1(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f22])).
% 1.67/0.59  fof(f22,plain,(
% 1.67/0.59    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.67/0.59    inference(definition_folding,[],[f15,f21,f20])).
% 1.67/0.59  fof(f20,plain,(
% 1.67/0.59    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 1.67/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.67/0.59  fof(f21,plain,(
% 1.67/0.59    ! [X0,X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> sP0(X1,X0,X2)) | ~sP1(X0,X1))),
% 1.67/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.67/0.59  fof(f15,plain,(
% 1.67/0.59    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.67/0.59    inference(flattening,[],[f14])).
% 1.67/0.59  fof(f14,plain,(
% 1.67/0.59    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.67/0.59    inference(ennf_transformation,[],[f2])).
% 1.67/0.59  fof(f2,axiom,(
% 1.67/0.59    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 1.67/0.59  fof(f152,plain,(
% 1.67/0.59    ( ! [X6,X4,X5] : (~m1_subset_1(X4,u1_struct_0(X5)) | ~r2_hidden(X4,X6) | ~l3_lattices(X5) | v2_struct_0(X5) | r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6)) | ~sP1(X5,X4)) )),
% 1.67/0.59    inference(resolution,[],[f150,f59])).
% 1.67/0.59  fof(f59,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | r4_lattice3(X0,X1,X2) | ~sP1(X0,X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f33])).
% 1.67/0.59  fof(f33,plain,(
% 1.67/0.59    ! [X0,X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | ~r4_lattice3(X0,X1,X2))) | ~sP1(X0,X1))),
% 1.67/0.59    inference(nnf_transformation,[],[f21])).
% 1.67/0.59  fof(f150,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (sP0(X0,X2,a_2_1_lattice3(X2,X1)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 1.67/0.59    inference(subsumption_resolution,[],[f149,f90])).
% 1.67/0.59  fof(f90,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (sP3(X0,sK9(X1,X0,X2)) | ~l3_lattices(X0) | v2_struct_0(X0) | sP0(X1,X0,X2)) )),
% 1.67/0.59    inference(resolution,[],[f71,f61])).
% 1.67/0.59  fof(f61,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f37])).
% 1.67/0.59  fof(f37,plain,(
% 1.67/0.59    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r1_lattices(X1,sK9(X0,X1,X2),X0) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 1.67/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f35,f36])).
% 1.67/0.59  fof(f36,plain,(
% 1.67/0.59    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,sK9(X0,X1,X2),X0) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))))),
% 1.67/0.59    introduced(choice_axiom,[])).
% 1.67/0.59  fof(f35,plain,(
% 1.67/0.59    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 1.67/0.59    inference(rectify,[],[f34])).
% 1.67/0.59  fof(f34,plain,(
% 1.67/0.59    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 1.67/0.59    inference(nnf_transformation,[],[f20])).
% 1.67/0.59  fof(f71,plain,(
% 1.67/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP3(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f25])).
% 1.67/0.59  fof(f25,plain,(
% 1.67/0.59    ! [X0] : (! [X1] : (sP3(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.67/0.59    inference(definition_folding,[],[f17,f24,f23])).
% 1.67/0.59  fof(f23,plain,(
% 1.67/0.59    ! [X1,X0,X2] : (sP2(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 1.67/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.67/0.59  fof(f24,plain,(
% 1.67/0.59    ! [X0,X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> sP2(X1,X0,X2)) | ~sP3(X0,X1))),
% 1.67/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.67/0.59  fof(f17,plain,(
% 1.67/0.59    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.67/0.59    inference(flattening,[],[f16])).
% 1.67/0.59  fof(f16,plain,(
% 1.67/0.59    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.67/0.59    inference(ennf_transformation,[],[f1])).
% 1.67/0.59  fof(f1,axiom,(
% 1.67/0.59    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 1.67/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 1.67/0.59  fof(f149,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~sP3(X2,sK9(X0,X2,a_2_1_lattice3(X2,X1))) | sP0(X0,X2,a_2_1_lattice3(X2,X1)) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 1.67/0.59    inference(duplicate_literal_removal,[],[f148])).
% 1.67/0.59  fof(f148,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~sP3(X2,sK9(X0,X2,a_2_1_lattice3(X2,X1))) | sP0(X0,X2,a_2_1_lattice3(X2,X1)) | ~l3_lattices(X2) | v2_struct_0(X2) | sP0(X0,X2,a_2_1_lattice3(X2,X1))) )),
% 1.67/0.59    inference(resolution,[],[f120,f129])).
% 1.67/0.59  fof(f129,plain,(
% 1.67/0.59    ( ! [X10,X8,X11,X9] : (r3_lattice3(X10,sK9(X8,X9,a_2_1_lattice3(X10,X11)),X11) | ~l3_lattices(X10) | v2_struct_0(X10) | sP0(X8,X9,a_2_1_lattice3(X10,X11))) )),
% 1.67/0.59    inference(resolution,[],[f126,f99])).
% 1.67/0.59  fof(f99,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | r3_lattice3(X1,X2,X0)) )),
% 1.67/0.59    inference(duplicate_literal_removal,[],[f98])).
% 1.67/0.59  fof(f98,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (r3_lattice3(X1,X2,X0) | ~sP4(X0,X1,X2) | ~sP4(X0,X1,X2)) )),
% 1.67/0.59    inference(superposition,[],[f76,f75])).
% 1.67/0.59  fof(f76,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK11(X0,X1,X2),X0) | ~sP4(X0,X1,X2)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f47])).
% 1.67/0.59  fof(f126,plain,(
% 1.67/0.59    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,sK9(X2,X3,a_2_1_lattice3(X1,X0))) | sP0(X2,X3,a_2_1_lattice3(X1,X0)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 1.67/0.59    inference(resolution,[],[f102,f78])).
% 1.67/0.59  fof(f102,plain,(
% 1.67/0.59    ( ! [X2,X0,X3,X1] : (~sP5(sK9(X2,X3,a_2_1_lattice3(X1,X0)),X1,X0) | sP4(X0,X1,sK9(X2,X3,a_2_1_lattice3(X1,X0))) | sP0(X2,X3,a_2_1_lattice3(X1,X0))) )),
% 1.67/0.59    inference(resolution,[],[f72,f62])).
% 1.67/0.59  fof(f62,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f37])).
% 1.67/0.59  fof(f72,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | sP4(X2,X1,X0) | ~sP5(X0,X1,X2)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f43])).
% 1.67/0.59  fof(f120,plain,(
% 1.67/0.59    ( ! [X2,X0,X3,X1] : (~r3_lattice3(X1,sK9(X0,X1,X3),X2) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~sP3(X1,sK9(X0,X1,X3)) | sP0(X0,X1,X3)) )),
% 1.67/0.59    inference(resolution,[],[f113,f63])).
% 1.67/0.59  fof(f63,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (~r1_lattices(X1,sK9(X0,X1,X2),X0) | sP0(X0,X1,X2)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f37])).
% 1.67/0.59  fof(f113,plain,(
% 1.67/0.59    ( ! [X2,X0,X3,X1] : (r1_lattices(X2,X3,X0) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~r3_lattice3(X2,X3,X1) | ~sP3(X2,X3)) )),
% 1.67/0.59    inference(resolution,[],[f67,f65])).
% 1.67/0.59  fof(f65,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | ~r3_lattice3(X0,X1,X2) | ~sP3(X0,X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f38])).
% 1.67/0.59  fof(f38,plain,(
% 1.67/0.59    ! [X0,X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ~sP2(X1,X0,X2)) & (sP2(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) | ~sP3(X0,X1))),
% 1.67/0.59    inference(nnf_transformation,[],[f24])).
% 1.67/0.59  fof(f67,plain,(
% 1.67/0.59    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f42])).
% 1.67/0.59  fof(f42,plain,(
% 1.67/0.59    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (~r1_lattices(X1,X0,sK10(X0,X1,X2)) & r2_hidden(sK10(X0,X1,X2),X2) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X0,X1,X2)))),
% 1.67/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f40,f41])).
% 1.67/0.59  fof(f41,plain,(
% 1.67/0.59    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK10(X0,X1,X2)) & r2_hidden(sK10(X0,X1,X2),X2) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))))),
% 1.67/0.59    introduced(choice_axiom,[])).
% 1.67/0.59  fof(f40,plain,(
% 1.67/0.59    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X0,X1,X2)))),
% 1.67/0.59    inference(rectify,[],[f39])).
% 1.67/0.59  fof(f39,plain,(
% 1.67/0.59    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP2(X1,X0,X2)))),
% 1.67/0.59    inference(nnf_transformation,[],[f23])).
% 1.67/0.59  fof(f55,plain,(
% 1.67/0.59    sK7 != k16_lattice3(sK6,sK8)),
% 1.67/0.59    inference(cnf_transformation,[],[f32])).
% 1.67/0.59  % SZS output end Proof for theBenchmark
% 1.67/0.59  % (19531)------------------------------
% 1.67/0.59  % (19531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.59  % (19531)Termination reason: Refutation
% 1.67/0.59  
% 1.67/0.59  % (19531)Memory used [KB]: 6268
% 1.67/0.59  % (19531)Time elapsed: 0.132 s
% 1.67/0.59  % (19531)------------------------------
% 1.67/0.59  % (19531)------------------------------
% 1.67/0.59  % (19526)Success in time 0.221 s
%------------------------------------------------------------------------------

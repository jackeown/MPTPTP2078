%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 156 expanded)
%              Number of leaves         :   14 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  391 (1093 expanded)
%              Number of equality atoms :   27 (  47 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(subsumption_resolution,[],[f178,f41])).

fof(f41,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( r2_hidden(sK6,k1_orders_2(sK5,sK7))
    & r2_hidden(sK6,sK7)
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l1_orders_2(sK5)
    & v5_orders_2(sK5)
    & v4_orders_2(sK5)
    & v3_orders_2(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f7,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( r2_hidden(X1,k1_orders_2(X0,X2))
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k1_orders_2(sK5,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) )
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l1_orders_2(sK5)
      & v5_orders_2(sK5)
      & v4_orders_2(sK5)
      & v3_orders_2(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( r2_hidden(X1,k1_orders_2(sK5,X2))
            & r2_hidden(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) )
        & m1_subset_1(X1,u1_struct_0(sK5)) )
   => ( ? [X2] :
          ( r2_hidden(sK6,k1_orders_2(sK5,X2))
          & r2_hidden(sK6,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) )
      & m1_subset_1(sK6,u1_struct_0(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( r2_hidden(sK6,k1_orders_2(sK5,X2))
        & r2_hidden(sK6,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) )
   => ( r2_hidden(sK6,k1_orders_2(sK5,sK7))
      & r2_hidden(sK6,sK7)
      & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k1_orders_2(X0,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k1_orders_2(X0,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r2_hidden(X1,k1_orders_2(X0,X2))
                    & r2_hidden(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( r2_hidden(X1,k1_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).

fof(f178,plain,(
    ~ l1_orders_2(sK5) ),
    inference(subsumption_resolution,[],[f175,f44])).

fof(f44,plain,(
    r2_hidden(sK6,sK7) ),
    inference(cnf_transformation,[],[f23])).

fof(f175,plain,
    ( ~ r2_hidden(sK6,sK7)
    | ~ l1_orders_2(sK5) ),
    inference(resolution,[],[f173,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X2,X0)
      | ~ l1_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ sP3(X0,X1,X2)
      | ~ l1_orders_2(X1)
      | ~ sP3(X0,X1,X2) ) ),
    inference(superposition,[],[f98,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( sK8(X0,X1,X2) = X2
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ! [X3] :
            ( ~ sP2(X3,X1,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( sP2(sK8(X0,X1,X2),X1,X0)
          & sK8(X0,X1,X2) = X2
          & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( sP2(X4,X1,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( sP2(sK8(X0,X1,X2),X1,X0)
        & sK8(X0,X1,X2) = X2
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ! [X3] :
            ( ~ sP2(X3,X1,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( sP2(X4,X1,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ( sP3(X2,X1,X0)
        | ! [X3] :
            ( ~ sP2(X3,X1,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( sP2(X3,X1,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP3(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( sP3(X2,X1,X0)
    <=> ? [X3] :
          ( sP2(X3,X1,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f98,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK8(X4,X5,X6),X4)
      | ~ sP3(X4,X5,X6)
      | ~ l1_orders_2(X5) ) ),
    inference(subsumption_resolution,[],[f96,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f96,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(sK8(X4,X5,X6),u1_struct_0(X5))
      | ~ r2_hidden(sK8(X4,X5,X6),X4)
      | ~ sP3(X4,X5,X6)
      | ~ l1_orders_2(X5) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(sK8(X4,X5,X6),u1_struct_0(X5))
      | ~ r2_hidden(sK8(X4,X5,X6),X4)
      | ~ sP3(X4,X5,X6)
      | ~ l1_orders_2(X5)
      | ~ m1_subset_1(sK8(X4,X5,X6),u1_struct_0(X5)) ) ),
    inference(resolution,[],[f79,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_orders_2(X1,X0,X0)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ r2_orders_2(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f78,f64])).

fof(f64,plain,(
    ! [X2,X1] : ~ sP0(X1,X1,X2) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( X0 != X1
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | X0 = X1
        | ~ r1_orders_2(X2,X1,X0) )
      & ( ( X0 != X1
          & r1_orders_2(X2,X1,X0) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | X1 = X2
        | ~ r1_orders_2(X0,X1,X2) )
      & ( ( X1 != X2
          & r1_orders_2(X0,X1,X2) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | X1 = X2
        | ~ r1_orders_2(X0,X1,X2) )
      & ( ( X1 != X2
          & r1_orders_2(X0,X1,X2) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ( X1 != X2
        & r1_orders_2(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f78,plain,(
    ! [X4,X5,X3] :
      ( sP0(X3,X5,X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ r2_orders_2(X4,X5,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X4)) ) ),
    inference(resolution,[],[f51,f46])).

% (26663)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% (26648)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% (26655)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (26648)Refutation not found, incomplete strategy% (26648)------------------------------
% (26648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26648)Termination reason: Refutation not found, incomplete strategy

% (26648)Memory used [KB]: 10618
% (26648)Time elapsed: 0.110 s
% (26648)------------------------------
% (26648)------------------------------
% (26650)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (26643)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (26642)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (26647)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (26642)Refutation not found, incomplete strategy% (26642)------------------------------
% (26642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26642)Termination reason: Refutation not found, incomplete strategy

% (26642)Memory used [KB]: 10618
% (26642)Time elapsed: 0.109 s
% (26642)------------------------------
% (26642)------------------------------
fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_orders_2(X0,X1,X2)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_orders_2(X0,X1,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_orders_2(X0,X1,X2)
      <=> sP0(X2,X1,X0) )
      | ~ sP1(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f8,f14,f13])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

% (26667)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_orders_2(X2,X0,sK8(X1,X2,X3))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ sP3(X1,X2,X3) ) ),
    inference(resolution,[],[f59,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sP2(sK8(X0,X1,X2),X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r2_orders_2(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ~ r2_orders_2(X1,sK9(X0,X1,X2),X0)
          & r2_hidden(sK9(X0,X1,X2),X2)
          & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_orders_2(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK9(X0,X1,X2),X0)
        & r2_hidden(sK9(X0,X1,X2),X2)
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ~ r2_orders_2(X1,X3,X0)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X3,X1,X2] :
      ( ( sP2(X3,X1,X2)
        | ? [X4] :
            ( ~ r2_orders_2(X1,X4,X3)
            & r2_hidden(X4,X2)
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X4,X3)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X3,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X3,X1,X2] :
      ( sP2(X3,X1,X2)
    <=> ! [X4] :
          ( r2_orders_2(X1,X4,X3)
          | ~ r2_hidden(X4,X2)
          | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f173,plain,(
    sP3(sK7,sK5,sK6) ),
    inference(subsumption_resolution,[],[f172,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f172,plain,
    ( sP3(sK7,sK5,sK6)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f171,f38])).

fof(f38,plain,(
    v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f171,plain,
    ( sP3(sK7,sK5,sK6)
    | ~ v3_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f170,f39])).

fof(f39,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f170,plain,
    ( sP3(sK7,sK5,sK6)
    | ~ v4_orders_2(sK5)
    | ~ v3_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f169,f40])).

fof(f40,plain,(
    v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f169,plain,
    ( sP3(sK7,sK5,sK6)
    | ~ v5_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v3_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f168,f41])).

fof(f168,plain,
    ( sP3(sK7,sK5,sK6)
    | ~ l1_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v3_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f164,f43])).

fof(f43,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f23])).

fof(f164,plain,
    ( sP3(sK7,sK5,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v3_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(resolution,[],[f107,f45])).

fof(f45,plain,(
    r2_hidden(sK6,k1_orders_2(sK5,sK7)) ),
    inference(cnf_transformation,[],[f23])).

fof(f107,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k1_orders_2(X3,X4))
      | sP3(X4,X3,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f105,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sP4(X0,X1,X2)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f12,f18,f17,f16])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> sP3(X2,X1,X0) )
      | ~ sP4(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f105,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k1_orders_2(X3,X4))
      | sP3(X4,X3,X5)
      | ~ sP4(X5,X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f53,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | sP3(X2,X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

% (26662)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (26646)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (26661)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (26660)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (26653)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (26659)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (26646)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f178,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    l1_orders_2(sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ((r2_hidden(sK6,k1_orders_2(sK5,sK7)) & r2_hidden(sK6,sK7) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))) & m1_subset_1(sK6,u1_struct_0(sK5))) & l1_orders_2(sK5) & v5_orders_2(sK5) & v4_orders_2(sK5) & v3_orders_2(sK5) & ~v2_struct_0(sK5)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f7,f22,f21,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (r2_hidden(X1,k1_orders_2(sK5,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))) & m1_subset_1(X1,u1_struct_0(sK5))) & l1_orders_2(sK5) & v5_orders_2(sK5) & v4_orders_2(sK5) & v3_orders_2(sK5) & ~v2_struct_0(sK5))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (r2_hidden(X1,k1_orders_2(sK5,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))) & m1_subset_1(X1,u1_struct_0(sK5))) => (? [X2] : (r2_hidden(sK6,k1_orders_2(sK5,X2)) & r2_hidden(sK6,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))) & m1_subset_1(sK6,u1_struct_0(sK5)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X2] : (r2_hidden(sK6,k1_orders_2(sK5,X2)) & r2_hidden(sK6,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))) => (r2_hidden(sK6,k1_orders_2(sK5,sK7)) & r2_hidden(sK6,sK7) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f6])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f4])).
% 0.21/0.51  fof(f4,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    ~l1_orders_2(sK5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f175,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    r2_hidden(sK6,sK7)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    ~r2_hidden(sK6,sK7) | ~l1_orders_2(sK5)),
% 0.21/0.51    inference(resolution,[],[f173,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | ~r2_hidden(X2,X0) | ~l1_orders_2(X1)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~sP3(X0,X1,X2) | ~l1_orders_2(X1) | ~sP3(X0,X1,X2)) )),
% 0.21/0.51    inference(superposition,[],[f98,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sK8(X0,X1,X2) = X2 | ~sP3(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ! [X3] : (~sP2(X3,X1,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((sP2(sK8(X0,X1,X2),X1,X0) & sK8(X0,X1,X2) = X2 & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f30,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X4] : (sP2(X4,X1,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (sP2(sK8(X0,X1,X2),X1,X0) & sK8(X0,X1,X2) = X2 & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ! [X3] : (~sP2(X3,X1,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (sP2(X4,X1,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 0.21/0.51    inference(rectify,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X2,X1,X0] : ((sP3(X2,X1,X0) | ! [X3] : (~sP2(X3,X1,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (sP2(X3,X1,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP3(X2,X1,X0)))),
% 0.21/0.51    inference(nnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (sP3(X2,X1,X0) <=> ? [X3] : (sP2(X3,X1,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X6,X4,X5] : (~r2_hidden(sK8(X4,X5,X6),X4) | ~sP3(X4,X5,X6) | ~l1_orders_2(X5)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f96,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) | ~sP3(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X6,X4,X5] : (~m1_subset_1(sK8(X4,X5,X6),u1_struct_0(X5)) | ~r2_hidden(sK8(X4,X5,X6),X4) | ~sP3(X4,X5,X6) | ~l1_orders_2(X5)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X6,X4,X5] : (~m1_subset_1(sK8(X4,X5,X6),u1_struct_0(X5)) | ~r2_hidden(sK8(X4,X5,X6),X4) | ~sP3(X4,X5,X6) | ~l1_orders_2(X5) | ~m1_subset_1(sK8(X4,X5,X6),u1_struct_0(X5))) )),
% 0.21/0.51    inference(resolution,[],[f79,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_orders_2(X1,X0,X0) | ~l1_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~r2_orders_2(X1,X0,X0) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.51    inference(resolution,[],[f78,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~sP0(X1,X1,X2)) )),
% 0.21/0.51    inference(equality_resolution,[],[f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (X0 != X1 | ~sP0(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | X0 = X1 | ~r1_orders_2(X2,X1,X0)) & ((X0 != X1 & r1_orders_2(X2,X1,X0)) | ~sP0(X0,X1,X2)))),
% 0.21/0.51    inference(rectify,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0)))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0)))),
% 0.21/0.51    inference(nnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> (X1 != X2 & r1_orders_2(X0,X1,X2)))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (sP0(X3,X5,X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~r2_orders_2(X4,X5,X3) | ~m1_subset_1(X3,u1_struct_0(X4))) )),
% 0.21/0.51    inference(resolution,[],[f51,f46])).
% 0.21/0.51  % (26663)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (26648)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (26655)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (26648)Refutation not found, incomplete strategy% (26648)------------------------------
% 0.21/0.52  % (26648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26648)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (26648)Memory used [KB]: 10618
% 0.21/0.52  % (26648)Time elapsed: 0.110 s
% 0.21/0.52  % (26648)------------------------------
% 0.21/0.52  % (26648)------------------------------
% 0.21/0.52  % (26650)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (26643)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (26642)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (26647)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (26642)Refutation not found, incomplete strategy% (26642)------------------------------
% 0.21/0.52  % (26642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26642)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (26642)Memory used [KB]: 10618
% 0.21/0.52  % (26642)Time elapsed: 0.109 s
% 0.21/0.52  % (26642)------------------------------
% 0.21/0.52  % (26642)------------------------------
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_orders_2(X0,X1,X2) | sP0(X2,X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_orders_2(X0,X1,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_orders_2(X0,X1,X2))) | ~sP1(X0,X1,X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_orders_2(X0,X1,X2) <=> sP0(X2,X1,X0)) | ~sP1(X0,X1,X2))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(definition_folding,[],[f8,f14,f13])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.52  % (26667)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_orders_2(X2,X0,sK8(X1,X2,X3)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~sP3(X1,X2,X3)) )),
% 0.21/0.52    inference(resolution,[],[f59,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP2(sK8(X0,X1,X2),X1,X0) | ~sP3(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r2_orders_2(X1,X4,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (~r2_orders_2(X1,sK9(X0,X1,X2),X0) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r2_orders_2(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X0,X1,X2)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f34,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : (~r2_orders_2(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r2_orders_2(X1,sK9(X0,X1,X2),X0) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (~r2_orders_2(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r2_orders_2(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X0,X1,X2)))),
% 0.21/0.52    inference(rectify,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X3,X1,X2] : ((sP2(X3,X1,X2) | ? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1)))) & (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X3,X1,X2)))),
% 0.21/0.52    inference(nnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X3,X1,X2] : (sP2(X3,X1,X2) <=> ! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    sP3(sK7,sK5,sK6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f172,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ~v2_struct_0(sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    sP3(sK7,sK5,sK6) | v2_struct_0(sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f171,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    v3_orders_2(sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    sP3(sK7,sK5,sK6) | ~v3_orders_2(sK5) | v2_struct_0(sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f170,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    v4_orders_2(sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    sP3(sK7,sK5,sK6) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f169,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    v5_orders_2(sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    sP3(sK7,sK5,sK6) | ~v5_orders_2(sK5) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f168,f41])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    sP3(sK7,sK5,sK6) | ~l1_orders_2(sK5) | ~v5_orders_2(sK5) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f164,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    sP3(sK7,sK5,sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_orders_2(sK5) | ~v5_orders_2(sK5) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5)),
% 0.21/0.52    inference(resolution,[],[f107,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    r2_hidden(sK6,k1_orders_2(sK5,sK7))),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (~r2_hidden(X5,k1_orders_2(X3,X4)) | sP3(X4,X3,X5) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_orders_2(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | v2_struct_0(X3)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f105,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sP4(X0,X1,X2) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (sP4(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.52    inference(definition_folding,[],[f12,f18,f17,f16])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> sP3(X2,X1,X0)) | ~sP4(X0,X1,X2))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (~r2_hidden(X5,k1_orders_2(X3,X4)) | sP3(X4,X3,X5) | ~sP4(X5,X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_orders_2(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | v2_struct_0(X3)) )),
% 0.21/0.52    inference(superposition,[],[f53,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | sP3(X2,X1,X0) | ~sP4(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  % (26662)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~sP3(X2,X1,X0)) & (sP3(X2,X1,X0) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~sP4(X0,X1,X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f18])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (26646)------------------------------
% 0.21/0.52  % (26646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26646)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (26646)Memory used [KB]: 6140
% 0.21/0.52  % (26646)Time elapsed: 0.107 s
% 0.21/0.52  % (26646)------------------------------
% 0.21/0.52  % (26646)------------------------------
% 0.21/0.53  % (26641)Success in time 0.166 s
%------------------------------------------------------------------------------

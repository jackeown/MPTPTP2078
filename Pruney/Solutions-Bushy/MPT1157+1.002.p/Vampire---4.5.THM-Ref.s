%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1157+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 781 expanded)
%              Number of leaves         :   20 ( 257 expanded)
%              Depth                    :   25
%              Number of atoms          :  783 (6918 expanded)
%              Number of equality atoms :   70 ( 180 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f697,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f88,f117,f127,f137,f635,f652,f696])).

fof(f696,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f695])).

fof(f695,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f694,f650])).

fof(f650,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1)))
    | spl6_2
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f86,f136])).

fof(f136,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl6_9
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f86,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_2
  <=> r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f694,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl6_1
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f693,f221])).

fof(f221,plain,
    ( k1_orders_2(sK0,k1_tarski(sK1)) = a_2_0_orders_2(sK0,k1_tarski(sK1))
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f220,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | ~ r2_orders_2(sK0,sK1,sK2) )
    & ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | r2_orders_2(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                  | ~ r2_orders_2(X0,X1,X2) )
                & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                  | r2_orders_2(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
                | ~ r2_orders_2(sK0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
                | r2_orders_2(sK0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
              | ~ r2_orders_2(sK0,X1,X2) )
            & ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
              | r2_orders_2(sK0,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
            | ~ r2_orders_2(sK0,sK1,X2) )
          & ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
            | r2_orders_2(sK0,sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
          | ~ r2_orders_2(sK0,sK1,X2) )
        & ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
          | r2_orders_2(sK0,sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | ~ r2_orders_2(sK0,sK1,sK2) )
      & ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | r2_orders_2(sK0,sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

% (5447)Refutation not found, incomplete strategy% (5447)------------------------------
% (5447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5447)Termination reason: Refutation not found, incomplete strategy

% (5447)Memory used [KB]: 10618
% (5447)Time elapsed: 0.124 s
% (5447)------------------------------
% (5447)------------------------------
% (5468)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (5466)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (5467)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% (5456)Refutation not found, incomplete strategy% (5456)------------------------------
% (5456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5456)Termination reason: Refutation not found, incomplete strategy

% (5456)Memory used [KB]: 10618
% (5456)Time elapsed: 0.087 s
% (5456)------------------------------
% (5456)------------------------------
% (5478)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% (5476)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_orders_2(X0,X1,X2)
                <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_orders_2)).

fof(f220,plain,
    ( k1_orders_2(sK0,k1_tarski(sK1)) = a_2_0_orders_2(sK0,k1_tarski(sK1))
    | v2_struct_0(sK0)
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f219,f47])).

fof(f47,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f219,plain,
    ( k1_orders_2(sK0,k1_tarski(sK1)) = a_2_0_orders_2(sK0,k1_tarski(sK1))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f218,f48])).

fof(f48,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f218,plain,
    ( k1_orders_2(sK0,k1_tarski(sK1)) = a_2_0_orders_2(sK0,k1_tarski(sK1))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f217,f49])).

fof(f49,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f217,plain,
    ( k1_orders_2(sK0,k1_tarski(sK1)) = a_2_0_orders_2(sK0,k1_tarski(sK1))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f212,f50])).

fof(f50,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f212,plain,
    ( k1_orders_2(sK0,k1_tarski(sK1)) = a_2_0_orders_2(sK0,k1_tarski(sK1))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(resolution,[],[f138,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

fof(f138,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f126,f136])).

fof(f126,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_7
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f693,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl6_1
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f692,f46])).

fof(f692,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f691,f47])).

fof(f691,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f690,f48])).

fof(f690,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f689,f49])).

fof(f689,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f688,f50])).

fof(f688,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f687,f138])).

fof(f687,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f686,f52])).

fof(f52,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f686,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f685,f81])).

fof(f81,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_1
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f685,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_28 ),
    inference(superposition,[],[f76,f676])).

fof(f676,plain,
    ( sK1 = sK4(sK0,k1_tarski(sK1),sK2)
    | ~ spl6_28 ),
    inference(resolution,[],[f648,f75])).

fof(f75,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f648,plain,
    ( r2_hidden(sK4(sK0,k1_tarski(sK1),sK2),k1_tarski(sK1))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f646])).

fof(f646,plain,
    ( spl6_28
  <=> r2_hidden(sK4(sK0,k1_tarski(sK1),sK2),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f76,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_orders_2(X1,sK4(X1,X2,X3),X3)
      | r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ r2_orders_2(X1,sK4(X1,X2,X3),X3)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,sK4(X1,X2,X3),X3)
                & r2_hidden(sK4(X1,X2,X3),X2)
                & m1_subset_1(sK4(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,X6,sK5(X0,X1,X2))
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK5(X0,X1,X2) = X0
            & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f42,f44,f43])).

fof(f43,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK4(X1,X2,X3),X3)
        & r2_hidden(sK4(X1,X2,X3),X2)
        & m1_subset_1(sK4(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X6,X5)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,X6,sK5(X0,X1,X2))
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK5(X0,X1,X2) = X0
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X6,X5)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X4,X3)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f652,plain,
    ( spl6_2
    | ~ spl6_7
    | ~ spl6_9
    | spl6_28 ),
    inference(avatar_contradiction_clause,[],[f651])).

fof(f651,plain,
    ( $false
    | spl6_2
    | ~ spl6_7
    | ~ spl6_9
    | spl6_28 ),
    inference(global_subsumption,[],[f277,f650,f647])).

fof(f647,plain,
    ( ~ r2_hidden(sK4(sK0,k1_tarski(sK1),sK2),k1_tarski(sK1))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f646])).

fof(f277,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1)))
    | r2_hidden(sK4(sK0,k1_tarski(sK1),sK2),k1_tarski(sK1))
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f275,f221])).

fof(f275,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | r2_hidden(sK4(sK0,k1_tarski(sK1),sK2),k1_tarski(sK1))
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(resolution,[],[f169,f138])).

fof(f169,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,a_2_0_orders_2(sK0,X1))
      | r2_hidden(sK4(sK0,X1,sK2),X1) ) ),
    inference(subsumption_resolution,[],[f168,f46])).

fof(f168,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,X1,sK2),X1)
      | r2_hidden(sK2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f167,f47])).

fof(f167,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,X1,sK2),X1)
      | r2_hidden(sK2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f166,f48])).

fof(f166,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,X1,sK2),X1)
      | r2_hidden(sK2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f165,f49])).

fof(f165,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,X1,sK2),X1)
      | r2_hidden(sK2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f159,f50])).

fof(f159,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,X1,sK2),X1)
      | r2_hidden(sK2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f77,f52])).

fof(f77,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(sK4(X1,X2,X3),X2)
      | r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | r2_hidden(sK4(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f635,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f634])).

fof(f634,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f633,f82])).

fof(f82,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f633,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f631,f628])).

fof(f628,plain,
    ( sK2 = sK5(sK2,sK0,k1_tarski(sK1))
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(resolution,[],[f497,f252])).

fof(f252,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(superposition,[],[f85,f136])).

fof(f85,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f497,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_orders_2(sK0,k1_tarski(sK1)))
        | sK5(X2,sK0,k1_tarski(sK1)) = X2 )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f496,f46])).

fof(f496,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_orders_2(sK0,k1_tarski(sK1)))
        | sK5(X2,sK0,k1_tarski(sK1)) = X2
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f495,f47])).

fof(f495,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_orders_2(sK0,k1_tarski(sK1)))
        | sK5(X2,sK0,k1_tarski(sK1)) = X2
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f494,f48])).

fof(f494,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_orders_2(sK0,k1_tarski(sK1)))
        | sK5(X2,sK0,k1_tarski(sK1)) = X2
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f493,f49])).

fof(f493,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_orders_2(sK0,k1_tarski(sK1)))
        | sK5(X2,sK0,k1_tarski(sK1)) = X2
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f492,f50])).

fof(f492,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_orders_2(sK0,k1_tarski(sK1)))
        | sK5(X2,sK0,k1_tarski(sK1)) = X2
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f478,f138])).

fof(f478,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_orders_2(sK0,k1_tarski(sK1)))
        | sK5(X2,sK0,k1_tarski(sK1)) = X2
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(superposition,[],[f67,f221])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | sK5(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f631,plain,
    ( r2_orders_2(sK0,sK1,sK5(sK2,sK0,k1_tarski(sK1)))
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(resolution,[],[f485,f252])).

fof(f485,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1)))
        | r2_orders_2(sK0,sK1,sK5(X0,sK0,k1_tarski(sK1))) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f484,f46])).

fof(f484,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1)))
        | r2_orders_2(sK0,sK1,sK5(X0,sK0,k1_tarski(sK1)))
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f483,f47])).

fof(f483,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1)))
        | r2_orders_2(sK0,sK1,sK5(X0,sK0,k1_tarski(sK1)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f482,f48])).

fof(f482,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1)))
        | r2_orders_2(sK0,sK1,sK5(X0,sK0,k1_tarski(sK1)))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f481,f49])).

fof(f481,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1)))
        | r2_orders_2(sK0,sK1,sK5(X0,sK0,k1_tarski(sK1)))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f480,f50])).

fof(f480,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1)))
        | r2_orders_2(sK0,sK1,sK5(X0,sK0,k1_tarski(sK1)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f479,f138])).

fof(f479,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1)))
        | r2_orders_2(sK0,sK1,sK5(X0,sK0,k1_tarski(sK1)))
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f476,f51])).

fof(f51,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f476,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1)))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | r2_orders_2(sK0,sK1,sK5(X0,sK0,k1_tarski(sK1)))
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(superposition,[],[f183,f221])).

fof(f183,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,a_2_0_orders_2(X2,k1_tarski(X3)))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | r2_orders_2(X2,X3,sK5(X4,X2,k1_tarski(X3)))
      | ~ m1_subset_1(k1_tarski(X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_orders_2(X2)
      | ~ v5_orders_2(X2)
      | ~ v4_orders_2(X2)
      | ~ v3_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f68,f74])).

fof(f74,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ r2_hidden(X6,X2)
      | r2_orders_2(X1,X6,sK5(X0,X1,X2))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f137,plain,
    ( spl6_4
    | spl6_9 ),
    inference(avatar_split_clause,[],[f110,f134,f101])).

fof(f101,plain,
    ( spl6_4
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f110,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f59,f51])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f127,plain,
    ( spl6_4
    | spl6_7 ),
    inference(avatar_split_clause,[],[f112,f124,f101])).

fof(f112,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f60,f51])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f117,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f115,f46])).

fof(f115,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f114,f90])).

fof(f90,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f55,f50])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f114,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f103,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f103,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f88,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f53,f84,f80])).

fof(f53,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f87,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f54,f84,f80])).

fof(f54,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

%------------------------------------------------------------------------------

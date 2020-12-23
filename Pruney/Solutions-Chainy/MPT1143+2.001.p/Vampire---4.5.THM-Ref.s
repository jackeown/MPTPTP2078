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
% DateTime   : Thu Dec  3 13:09:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 782 expanded)
%              Number of leaves         :   20 ( 232 expanded)
%              Depth                    :   24
%              Number of atoms          :  367 (3562 expanded)
%              Number of equality atoms :   34 (  90 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (18365)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (18374)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f355,plain,(
    $false ),
    inference(subsumption_resolution,[],[f347,f134])).

fof(f134,plain,(
    r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3)) ),
    inference(subsumption_resolution,[],[f133,f57])).

fof(f57,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f42])).

% (18367)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (18354)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (18365)Refutation not found, incomplete strategy% (18365)------------------------------
% (18365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18376)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (18375)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% (18370)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% (18373)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (18360)Termination reason: Refutation not found, incomplete strategy

% (18360)Memory used [KB]: 10618
% (18360)Time elapsed: 0.085 s
% (18360)------------------------------
% (18360)------------------------------
fof(f42,plain,
    ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK3),sK4),sK3) )
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f41,f40])).

% (18361)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK3)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK3),X1),sK3) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK3)))
          | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK3),X1),sK3) )
        & m1_subset_1(X1,u1_struct_0(sK3)) )
   => ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK3),sK4),sK3) )
      & m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

fof(f133,plain,
    ( r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(subsumption_resolution,[],[f132,f58])).

fof(f58,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f132,plain,
    ( r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,
    ( r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(resolution,[],[f117,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f117,plain,(
    r1_orders_2(sK3,sK4,sK4) ),
    inference(subsumption_resolution,[],[f116,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f116,plain,
    ( r1_orders_2(sK3,sK4,sK4)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f115,f56])).

fof(f56,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f115,plain,
    ( r1_orders_2(sK3,sK4,sK4)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f107,f57])).

fof(f107,plain,
    ( r1_orders_2(sK3,sK4,sK4)
    | ~ l1_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f58,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f347,plain,(
    ~ r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3)) ),
    inference(backward_demodulation,[],[f273,f339])).

fof(f339,plain,(
    sK4 = sK6(u1_orders_2(sK3),k1_tarski(sK4)) ),
    inference(resolution,[],[f220,f88])).

fof(f88,plain,(
    ! [X0] : sP2(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP2(X0,X1) )
      & ( sP2(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP2(X0,X1) ) ),
    inference(definition_folding,[],[f1,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f220,plain,(
    ! [X0] :
      ( ~ sP2(X0,k1_tarski(sK4))
      | sK6(u1_orders_2(sK3),k1_tarski(sK4)) = X0 ) ),
    inference(resolution,[],[f198,f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
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
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
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
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f198,plain,(
    r2_hidden(sK6(u1_orders_2(sK3),k1_tarski(sK4)),k1_tarski(sK4)) ),
    inference(resolution,[],[f194,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
          & ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
          & r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X1) ) )
      & ( ! [X4,X5] :
            ( r2_hidden(k4_tarski(X5,X4),X0)
            | r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
        & r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            & ~ r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) ) )
      & ( ! [X4,X5] :
            ( r2_hidden(k4_tarski(X5,X4),X0)
            | r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            & ~ r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) ) )
      & ( ! [X2,X3] :
            ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2,X3] :
          ( r2_hidden(k4_tarski(X3,X2),X0)
          | r2_hidden(k4_tarski(X2,X3),X0)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f194,plain,(
    ~ sP0(u1_orders_2(sK3),k1_tarski(sK4)) ),
    inference(resolution,[],[f193,f170])).

fof(f170,plain,
    ( ~ sP1(u1_orders_2(sK3))
    | ~ sP0(u1_orders_2(sK3),k1_tarski(sK4)) ),
    inference(resolution,[],[f168,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,X1)
      | ~ sP0(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | ~ r7_relat_2(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f168,plain,(
    ~ r7_relat_2(u1_orders_2(sK3),k1_tarski(sK4)) ),
    inference(subsumption_resolution,[],[f167,f57])).

fof(f167,plain,
    ( ~ r7_relat_2(u1_orders_2(sK3),k1_tarski(sK4))
    | ~ l1_orders_2(sK3) ),
    inference(subsumption_resolution,[],[f165,f136])).

fof(f136,plain,(
    m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f124,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f124,plain,(
    r2_hidden(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f114,f103])).

fof(f103,plain,(
    ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f102,f55])).

fof(f102,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f93,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f93,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f57,f68])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f114,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f58,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f165,plain,
    ( ~ r7_relat_2(u1_orders_2(sK3),k1_tarski(sK4))
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_orders_2(sK3) ),
    inference(resolution,[],[f164,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v6_orders_2(X1,X0)
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

fof(f164,plain,(
    ~ v6_orders_2(k1_tarski(sK4),sK3) ),
    inference(subsumption_resolution,[],[f147,f136])).

fof(f147,plain,
    ( ~ v6_orders_2(k1_tarski(sK4),sK3)
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_demodulation,[],[f145,f123])).

fof(f123,plain,(
    k6_domain_1(u1_struct_0(sK3),sK4) = k1_tarski(sK4) ),
    inference(subsumption_resolution,[],[f113,f103])).

fof(f113,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k1_tarski(sK4)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f58,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f145,plain,
    ( ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK3),sK4),sK3) ),
    inference(backward_demodulation,[],[f59,f123])).

fof(f59,plain,
    ( ~ v6_orders_2(k6_domain_1(u1_struct_0(sK3),sK4),sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f42])).

fof(f193,plain,(
    sP1(u1_orders_2(sK3)) ),
    inference(resolution,[],[f189,f67])).

fof(f67,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f18,f36,f35])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_2)).

fof(f189,plain,(
    v1_relat_1(u1_orders_2(sK3)) ),
    inference(resolution,[],[f94,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f94,plain,(
    m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) ),
    inference(resolution,[],[f57,f69])).

fof(f69,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f273,plain,(
    ~ r2_hidden(k4_tarski(sK4,sK6(u1_orders_2(sK3),k1_tarski(sK4))),u1_orders_2(sK3)) ),
    inference(subsumption_resolution,[],[f270,f194])).

fof(f270,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK6(u1_orders_2(sK3),k1_tarski(sK4))),u1_orders_2(sK3))
    | sP0(u1_orders_2(sK3),k1_tarski(sK4)) ),
    inference(superposition,[],[f65,f260])).

fof(f260,plain,(
    sK4 = sK5(u1_orders_2(sK3),k1_tarski(sK4)) ),
    inference(resolution,[],[f215,f88])).

fof(f215,plain,(
    ! [X0] :
      ( ~ sP2(X0,k1_tarski(sK4))
      | sK5(u1_orders_2(sK3),k1_tarski(sK4)) = X0 ) ),
    inference(resolution,[],[f197,f80])).

fof(f197,plain,(
    r2_hidden(sK5(u1_orders_2(sK3),k1_tarski(sK4)),k1_tarski(sK4)) ),
    inference(resolution,[],[f194,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:02:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (18362)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (18356)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (18368)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (18358)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (18360)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (18359)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (18357)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (18369)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (18360)Refutation not found, incomplete strategy% (18360)------------------------------
% 0.22/0.51  % (18360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18363)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (18362)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  % (18365)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (18374)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  fof(f355,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f347,f134])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3))),
% 0.22/0.52    inference(subsumption_resolution,[],[f133,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    l1_orders_2(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  % (18367)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (18354)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (18365)Refutation not found, incomplete strategy% (18365)------------------------------
% 0.22/0.52  % (18365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18376)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (18375)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (18370)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (18373)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.53  % (18360)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (18360)Memory used [KB]: 10618
% 0.22/0.53  % (18360)Time elapsed: 0.085 s
% 0.22/0.53  % (18360)------------------------------
% 0.22/0.53  % (18360)------------------------------
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ((~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) | ~v6_orders_2(k6_domain_1(u1_struct_0(sK3),sK4),sK3)) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f41,f40])).
% 0.22/0.53  % (18361)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK3))) | ~v6_orders_2(k6_domain_1(u1_struct_0(sK3),X1),sK3)) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ? [X1] : ((~m1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK3))) | ~v6_orders_2(k6_domain_1(u1_struct_0(sK3),X1),sK3)) & m1_subset_1(X1,u1_struct_0(sK3))) => ((~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) | ~v6_orders_2(k6_domain_1(u1_struct_0(sK3),sK4),sK3)) & m1_subset_1(sK4,u1_struct_0(sK3)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.53    inference(negated_conjecture,[],[f14])).
% 0.22/0.53  fof(f14,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3)) | ~l1_orders_2(sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f132,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_orders_2(sK3)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f131])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_orders_2(sK3)),
% 0.22/0.53    inference(resolution,[],[f117,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    r1_orders_2(sK3,sK4,sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f116,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ~v2_struct_0(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    r1_orders_2(sK3,sK4,sK4) | v2_struct_0(sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f115,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    v3_orders_2(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    r1_orders_2(sK3,sK4,sK4) | ~v3_orders_2(sK3) | v2_struct_0(sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f107,f57])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    r1_orders_2(sK3,sK4,sK4) | ~l1_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)),
% 0.22/0.53    inference(resolution,[],[f58,f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).
% 0.22/0.53  fof(f347,plain,(
% 0.22/0.53    ~r2_hidden(k4_tarski(sK4,sK4),u1_orders_2(sK3))),
% 0.22/0.53    inference(backward_demodulation,[],[f273,f339])).
% 0.22/0.53  fof(f339,plain,(
% 0.22/0.53    sK4 = sK6(u1_orders_2(sK3),k1_tarski(sK4))),
% 0.22/0.53    inference(resolution,[],[f220,f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ( ! [X0] : (sP2(X0,k1_tarski(X0))) )),
% 0.22/0.53    inference(equality_resolution,[],[f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP2(X0,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ~sP2(X0,X1)) & (sP2(X0,X1) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> sP2(X0,X1))),
% 0.22/0.53    inference(definition_folding,[],[f1,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1] : (sP2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    ( ! [X0] : (~sP2(X0,k1_tarski(sK4)) | sK6(u1_orders_2(sK3),k1_tarski(sK4)) = X0) )),
% 0.22/0.53    inference(resolution,[],[f198,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | ~sP2(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP2(X0,X1) | ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP2(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f51,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP2(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | ~sP2(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f38])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    r2_hidden(sK6(u1_orders_2(sK3),k1_tarski(sK4)),k1_tarski(sK4))),
% 0.22/0.53    inference(resolution,[],[f194,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(sK6(X0,X1),X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP0(X0,X1) | (~r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) & ~r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1))) & (! [X4,X5] : (r2_hidden(k4_tarski(X5,X4),X0) | r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f45,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) & ~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (~r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) & ~r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) & ~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X4,X5] : (r2_hidden(k4_tarski(X5,X4),X0) | r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) & ~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X2,X3] : (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) | ~sP0(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    ~sP0(u1_orders_2(sK3),k1_tarski(sK4))),
% 0.22/0.53    inference(resolution,[],[f193,f170])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    ~sP1(u1_orders_2(sK3)) | ~sP0(u1_orders_2(sK3),k1_tarski(sK4))),
% 0.22/0.53    inference(resolution,[],[f168,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r7_relat_2(X0,X1) | ~sP0(X0,X1) | ~sP1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((r7_relat_2(X0,X1) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~r7_relat_2(X0,X1))) | ~sP1(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r7_relat_2(X0,X1) <=> sP0(X0,X1)) | ~sP1(X0))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    ~r7_relat_2(u1_orders_2(sK3),k1_tarski(sK4))),
% 0.22/0.53    inference(subsumption_resolution,[],[f167,f57])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    ~r7_relat_2(u1_orders_2(sK3),k1_tarski(sK4)) | ~l1_orders_2(sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f165,f136])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.53    inference(resolution,[],[f124,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    r2_hidden(sK4,u1_struct_0(sK3))),
% 0.22/0.53    inference(subsumption_resolution,[],[f114,f103])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ~v1_xboole_0(u1_struct_0(sK3))),
% 0.22/0.53    inference(subsumption_resolution,[],[f102,f55])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ~v1_xboole_0(u1_struct_0(sK3)) | v2_struct_0(sK3)),
% 0.22/0.53    inference(resolution,[],[f93,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    l1_struct_0(sK3)),
% 0.22/0.53    inference(resolution,[],[f57,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    r2_hidden(sK4,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3))),
% 0.22/0.53    inference(resolution,[],[f58,f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    ~r7_relat_2(u1_orders_2(sK3),k1_tarski(sK4)) | ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_orders_2(sK3)),
% 0.22/0.53    inference(resolution,[],[f164,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v6_orders_2(X1,X0) | ~r7_relat_2(u1_orders_2(X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((v6_orders_2(X1,X0) | ~r7_relat_2(u1_orders_2(X0),X1)) & (r7_relat_2(u1_orders_2(X0),X1) | ~v6_orders_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    ~v6_orders_2(k1_tarski(sK4),sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f147,f136])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    ~v6_orders_2(k1_tarski(sK4),sK3) | ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.53    inference(forward_demodulation,[],[f145,f123])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    k6_domain_1(u1_struct_0(sK3),sK4) = k1_tarski(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f113,f103])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    k6_domain_1(u1_struct_0(sK3),sK4) = k1_tarski(sK4) | v1_xboole_0(u1_struct_0(sK3))),
% 0.22/0.53    inference(resolution,[],[f58,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK3))) | ~v6_orders_2(k6_domain_1(u1_struct_0(sK3),sK4),sK3)),
% 0.22/0.53    inference(backward_demodulation,[],[f59,f123])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ~v6_orders_2(k6_domain_1(u1_struct_0(sK3),sK4),sK3) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    sP1(u1_orders_2(sK3))),
% 0.22/0.53    inference(resolution,[],[f189,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X0] : (sP1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(definition_folding,[],[f18,f36,f35])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r7_relat_2(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r7_relat_2(X0,X1) <=> ! [X2,X3] : ~(~r2_hidden(k4_tarski(X3,X2),X0) & ~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_2)).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    v1_relat_1(u1_orders_2(sK3))),
% 0.22/0.53    inference(resolution,[],[f94,f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))),
% 0.22/0.53    inference(resolution,[],[f57,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.22/0.53  fof(f273,plain,(
% 0.22/0.53    ~r2_hidden(k4_tarski(sK4,sK6(u1_orders_2(sK3),k1_tarski(sK4))),u1_orders_2(sK3))),
% 0.22/0.53    inference(subsumption_resolution,[],[f270,f194])).
% 0.22/0.53  fof(f270,plain,(
% 0.22/0.53    ~r2_hidden(k4_tarski(sK4,sK6(u1_orders_2(sK3),k1_tarski(sK4))),u1_orders_2(sK3)) | sP0(u1_orders_2(sK3),k1_tarski(sK4))),
% 0.22/0.53    inference(superposition,[],[f65,f260])).
% 0.22/0.53  fof(f260,plain,(
% 0.22/0.53    sK4 = sK5(u1_orders_2(sK3),k1_tarski(sK4))),
% 0.22/0.53    inference(resolution,[],[f215,f88])).
% 0.22/0.53  fof(f215,plain,(
% 0.22/0.53    ( ! [X0] : (~sP2(X0,k1_tarski(sK4)) | sK5(u1_orders_2(sK3),k1_tarski(sK4)) = X0) )),
% 0.22/0.53    inference(resolution,[],[f197,f80])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    r2_hidden(sK5(u1_orders_2(sK3),k1_tarski(sK4)),k1_tarski(sK4))),
% 0.22/0.53    inference(resolution,[],[f194,f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(sK5(X0,X1),X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f47])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP0(X0,X1) | ~r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f47])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (18362)------------------------------
% 0.22/0.53  % (18362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18362)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (18362)Memory used [KB]: 1791
% 0.22/0.53  % (18362)Time elapsed: 0.097 s
% 0.22/0.53  % (18362)------------------------------
% 0.22/0.53  % (18362)------------------------------
% 0.22/0.53  % (18353)Success in time 0.162 s
%------------------------------------------------------------------------------

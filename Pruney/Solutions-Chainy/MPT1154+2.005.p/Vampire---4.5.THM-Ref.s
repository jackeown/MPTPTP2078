%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 121 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :  181 ( 545 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(subsumption_resolution,[],[f86,f69])).

fof(f69,plain,(
    r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1))) ),
    inference(backward_demodulation,[],[f29,f66])).

fof(f66,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(resolution,[],[f55,f63])).

fof(f63,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f62,f30])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_orders_2)).

fof(f62,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f53,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f53,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f34,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

% (5577)Refutation not found, incomplete strategy% (5577)------------------------------
% (5577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5577)Termination reason: Refutation not found, incomplete strategy

% (5577)Memory used [KB]: 10618
% (5577)Time elapsed: 0.124 s
% (5577)------------------------------
% (5577)------------------------------
% (5584)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (5589)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (5590)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (5594)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% (5591)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (5586)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% (5581)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f34,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(resolution,[],[f28,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f28,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f86,plain,(
    ~ r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1))) ),
    inference(subsumption_resolution,[],[f81,f52])).

fof(f52,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f81,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1))) ),
    inference(resolution,[],[f76,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X0)
      | ~ r2_hidden(sK1,k1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f60,f30])).

fof(f60,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X0)
      | ~ r2_hidden(sK1,k1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f59,f34])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X0)
      | ~ r2_hidden(sK1,k1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f58,f33])).

fof(f33,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X0)
      | ~ r2_hidden(sK1,k1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f57,f32])).

fof(f32,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X0)
      | ~ r2_hidden(sK1,k1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f54,f31])).

fof(f31,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X0)
      | ~ r2_hidden(sK1,k1_orders_2(sK0,X0)) ) ),
    inference(resolution,[],[f28,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k1_orders_2(X0,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f76,plain,(
    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f74,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f74,plain,(
    r1_tarski(k1_tarski(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f72,f63])).

fof(f72,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r1_tarski(k1_tarski(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f56,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f56,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f28,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:07:22 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.21/0.56  % (5574)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.56  % (5573)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.56  % (5576)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.56  % (5575)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.56  % (5577)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.56  % (5576)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(subsumption_resolution,[],[f86,f69])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1)))),
% 0.21/0.56    inference(backward_demodulation,[],[f29,f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 0.21/0.56    inference(resolution,[],[f55,f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.56    inference(subsumption_resolution,[],[f62,f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ~v2_struct_0(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,negated_conjecture,(
% 0.21/0.56    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.21/0.56    inference(negated_conjecture,[],[f12])).
% 0.21/0.56  fof(f12,conjecture,(
% 0.21/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_orders_2)).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    v2_struct_0(sK0) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.56    inference(resolution,[],[f53,f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X0] : (~l1_struct_0(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    l1_struct_0(sK0)),
% 0.21/0.56    inference(resolution,[],[f34,f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  % (5577)Refutation not found, incomplete strategy% (5577)------------------------------
% 0.21/0.56  % (5577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5577)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5577)Memory used [KB]: 10618
% 0.21/0.56  % (5577)Time elapsed: 0.124 s
% 0.21/0.56  % (5577)------------------------------
% 0.21/0.56  % (5577)------------------------------
% 0.21/0.56  % (5584)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.57  % (5589)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.57  % (5590)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.57  % (5594)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.57  % (5591)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.57  % (5586)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.59/0.57  % (5581)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.59/0.57  fof(f9,axiom,(
% 1.59/0.57    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.59/0.57  fof(f34,plain,(
% 1.59/0.57    l1_orders_2(sK0)),
% 1.59/0.57    inference(cnf_transformation,[],[f15])).
% 1.59/0.57  fof(f55,plain,(
% 1.59/0.57    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 1.59/0.57    inference(resolution,[],[f28,f39])).
% 1.59/0.57  fof(f39,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f24])).
% 1.59/0.57  fof(f24,plain,(
% 1.59/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.59/0.57    inference(flattening,[],[f23])).
% 1.59/0.57  fof(f23,plain,(
% 1.59/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.59/0.57    inference(ennf_transformation,[],[f10])).
% 1.59/0.57  fof(f10,axiom,(
% 1.59/0.57    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.59/0.57  fof(f28,plain,(
% 1.59/0.57    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.59/0.57    inference(cnf_transformation,[],[f15])).
% 1.59/0.57  fof(f29,plain,(
% 1.59/0.57    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 1.59/0.57    inference(cnf_transformation,[],[f15])).
% 1.59/0.57  fof(f86,plain,(
% 1.59/0.57    ~r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1)))),
% 1.59/0.57    inference(subsumption_resolution,[],[f81,f52])).
% 1.59/0.57  fof(f52,plain,(
% 1.59/0.57    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 1.59/0.57    inference(equality_resolution,[],[f51])).
% 1.59/0.57  fof(f51,plain,(
% 1.59/0.57    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 1.59/0.57    inference(equality_resolution,[],[f44])).
% 1.59/0.57  fof(f44,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.59/0.57    inference(cnf_transformation,[],[f2])).
% 1.59/0.57  fof(f2,axiom,(
% 1.59/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.59/0.57  fof(f81,plain,(
% 1.59/0.57    ~r2_hidden(sK1,k1_tarski(sK1)) | ~r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1)))),
% 1.59/0.57    inference(resolution,[],[f76,f61])).
% 1.59/0.57  fof(f61,plain,(
% 1.59/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X0) | ~r2_hidden(sK1,k1_orders_2(sK0,X0))) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f60,f30])).
% 1.59/0.57  fof(f60,plain,(
% 1.59/0.57    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X0) | ~r2_hidden(sK1,k1_orders_2(sK0,X0))) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f59,f34])).
% 1.59/0.57  fof(f59,plain,(
% 1.59/0.57    ( ! [X0] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X0) | ~r2_hidden(sK1,k1_orders_2(sK0,X0))) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f58,f33])).
% 1.59/0.57  fof(f33,plain,(
% 1.59/0.57    v5_orders_2(sK0)),
% 1.59/0.57    inference(cnf_transformation,[],[f15])).
% 1.59/0.57  fof(f58,plain,(
% 1.59/0.57    ( ! [X0] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X0) | ~r2_hidden(sK1,k1_orders_2(sK0,X0))) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f57,f32])).
% 1.59/0.57  fof(f32,plain,(
% 1.59/0.57    v4_orders_2(sK0)),
% 1.59/0.57    inference(cnf_transformation,[],[f15])).
% 1.59/0.57  fof(f57,plain,(
% 1.59/0.57    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X0) | ~r2_hidden(sK1,k1_orders_2(sK0,X0))) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f54,f31])).
% 1.59/0.57  fof(f31,plain,(
% 1.59/0.57    v3_orders_2(sK0)),
% 1.59/0.57    inference(cnf_transformation,[],[f15])).
% 1.59/0.57  fof(f54,plain,(
% 1.59/0.57    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X0) | ~r2_hidden(sK1,k1_orders_2(sK0,X0))) )),
% 1.59/0.57    inference(resolution,[],[f28,f38])).
% 1.59/0.57  fof(f38,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,k1_orders_2(X0,X2))) )),
% 1.59/0.57    inference(cnf_transformation,[],[f22])).
% 1.59/0.57  fof(f22,plain,(
% 1.59/0.57    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.59/0.57    inference(flattening,[],[f21])).
% 1.59/0.57  fof(f21,plain,(
% 1.59/0.57    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.59/0.57    inference(ennf_transformation,[],[f11])).
% 1.59/0.57  fof(f11,axiom,(
% 1.59/0.57    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).
% 1.59/0.57  fof(f76,plain,(
% 1.59/0.57    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.59/0.57    inference(resolution,[],[f74,f42])).
% 1.59/0.57  fof(f42,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.59/0.57    inference(cnf_transformation,[],[f5])).
% 1.59/0.57  fof(f5,axiom,(
% 1.59/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.59/0.57  fof(f74,plain,(
% 1.59/0.57    r1_tarski(k1_tarski(sK1),u1_struct_0(sK0))),
% 1.59/0.57    inference(subsumption_resolution,[],[f72,f63])).
% 1.59/0.57  fof(f72,plain,(
% 1.59/0.57    v1_xboole_0(u1_struct_0(sK0)) | r1_tarski(k1_tarski(sK1),u1_struct_0(sK0))),
% 1.59/0.57    inference(resolution,[],[f56,f48])).
% 1.59/0.57  fof(f48,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f3])).
% 1.59/0.57  fof(f3,axiom,(
% 1.59/0.57    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.59/0.57  fof(f56,plain,(
% 1.59/0.57    r2_hidden(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 1.59/0.57    inference(resolution,[],[f28,f37])).
% 1.59/0.57  fof(f37,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f20])).
% 1.59/0.57  fof(f20,plain,(
% 1.59/0.57    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.59/0.57    inference(flattening,[],[f19])).
% 1.59/0.57  fof(f19,plain,(
% 1.59/0.57    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.59/0.57    inference(ennf_transformation,[],[f4])).
% 1.59/0.57  fof(f4,axiom,(
% 1.59/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.59/0.57  % SZS output end Proof for theBenchmark
% 1.59/0.57  % (5576)------------------------------
% 1.59/0.57  % (5576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (5576)Termination reason: Refutation
% 1.59/0.57  
% 1.59/0.57  % (5576)Memory used [KB]: 6140
% 1.59/0.57  % (5576)Time elapsed: 0.125 s
% 1.59/0.57  % (5576)------------------------------
% 1.59/0.57  % (5576)------------------------------
% 1.59/0.57  % (5570)Success in time 0.207 s
%------------------------------------------------------------------------------

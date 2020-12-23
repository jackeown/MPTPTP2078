%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 137 expanded)
%              Number of leaves         :    5 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  171 ( 706 expanded)
%              Number of equality atoms :   21 (  99 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(subsumption_resolution,[],[f98,f93])).

fof(f93,plain,(
    r2_hidden(sK1,k5_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f92,f22])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X2,k6_tmap_1(X0,X1))
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X2,k6_tmap_1(X0,X1))
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
               => ( X1 = X2
                 => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).

fof(f92,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK1,k5_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f91,f21])).

fof(f21,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

% (17635)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
fof(f91,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK1,k5_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f72,f20])).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f72,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK1,k5_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f19,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,k5_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r2_hidden(X1,k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tmap_1)).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f98,plain,(
    ~ r2_hidden(sK1,k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f97,f81])).

fof(f81,plain,(
    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f80,f22])).

fof(f80,plain,
    ( ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f79,f21])).

fof(f79,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f68,f20])).

fof(f68,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f19,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f97,plain,(
    ~ r2_hidden(sK1,u1_pre_topc(k6_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f96,f19])).

fof(f96,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,u1_pre_topc(k6_tmap_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f95,f77])).

fof(f77,plain,(
    u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f76,f22])).

fof(f76,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f75,f21])).

fof(f75,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f67,f20])).

fof(f67,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
    inference(resolution,[],[f19,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f95,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
    | ~ r2_hidden(sK1,u1_pre_topc(k6_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f94,f90])).

fof(f90,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f89,f22])).

fof(f89,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f88,f21])).

fof(f88,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f71,f20])).

fof(f71,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f19,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | l1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f94,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
    | ~ r2_hidden(sK1,u1_pre_topc(k6_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f31,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f31,plain,(
    ~ v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f18,f17])).

fof(f17,plain,(
    sK1 = sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f18,plain,(
    ~ v3_pre_topc(sK2,k6_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:52:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (17620)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.48  % (17618)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.49  % (17624)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.49  % (17617)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.49  % (17624)Refutation not found, incomplete strategy% (17624)------------------------------
% 0.20/0.49  % (17624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (17624)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (17624)Memory used [KB]: 10618
% 0.20/0.49  % (17624)Time elapsed: 0.068 s
% 0.20/0.49  % (17624)------------------------------
% 0.20/0.49  % (17624)------------------------------
% 0.20/0.49  % (17616)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.49  % (17631)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.49  % (17628)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.49  % (17621)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (17625)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.50  % (17637)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (17636)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.50  % (17626)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.50  % (17637)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f98,f93])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    r2_hidden(sK1,k5_tmap_1(sK0,sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f92,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (~v3_pre_topc(X2,k6_tmap_1(X0,X1)) & X1 = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f7])).
% 0.20/0.50  fof(f7,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((~v3_pre_topc(X2,k6_tmap_1(X0,X1)) & X1 = X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f5])).
% 0.20/0.50  fof(f5,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | r2_hidden(sK1,k5_tmap_1(sK0,sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f91,f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    v2_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  % (17635)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | r2_hidden(sK1,k5_tmap_1(sK0,sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f72,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | r2_hidden(sK1,k5_tmap_1(sK0,sK1))),
% 0.20/0.50    inference(resolution,[],[f19,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,k5_tmap_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (r2_hidden(X1,k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (r2_hidden(X1,k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r2_hidden(X1,k5_tmap_1(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tmap_1)).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ~r2_hidden(sK1,k5_tmap_1(sK0,sK1))),
% 0.20/0.50    inference(forward_demodulation,[],[f97,f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f80,f22])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f79,f21])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f68,f20])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.20/0.50    inference(resolution,[],[f19,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    ~r2_hidden(sK1,u1_pre_topc(k6_tmap_1(sK0,sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f96,f19])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,u1_pre_topc(k6_tmap_1(sK0,sK1)))),
% 0.20/0.50    inference(forward_demodulation,[],[f95,f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f76,f22])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f75,f21])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f67,f20])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f19,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~r2_hidden(sK1,u1_pre_topc(k6_tmap_1(sK0,sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f94,f90])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f89,f22])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f88,f21])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f71,f20])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.20/0.50    inference(resolution,[],[f19,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | l1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~r2_hidden(sK1,u1_pre_topc(k6_tmap_1(sK0,sK1)))),
% 0.20/0.50    inference(resolution,[],[f31,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ~v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 0.20/0.50    inference(backward_demodulation,[],[f18,f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    sK1 = sK2),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ~v3_pre_topc(sK2,k6_tmap_1(sK0,sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (17637)------------------------------
% 0.20/0.50  % (17637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (17637)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (17637)Memory used [KB]: 1663
% 0.20/0.50  % (17637)Time elapsed: 0.091 s
% 0.20/0.50  % (17637)------------------------------
% 0.20/0.50  % (17637)------------------------------
% 0.20/0.50  % (17636)Refutation not found, incomplete strategy% (17636)------------------------------
% 0.20/0.50  % (17636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (17636)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (17636)Memory used [KB]: 6140
% 0.20/0.50  % (17636)Time elapsed: 0.089 s
% 0.20/0.50  % (17636)------------------------------
% 0.20/0.50  % (17636)------------------------------
% 0.20/0.50  % (17638)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (17615)Success in time 0.141 s
%------------------------------------------------------------------------------

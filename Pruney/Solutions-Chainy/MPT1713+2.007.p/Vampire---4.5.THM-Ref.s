%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:51 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 338 expanded)
%              Number of leaves         :   10 (  62 expanded)
%              Depth                    :   20
%              Number of atoms          :  203 (1781 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f144,plain,(
    $false ),
    inference(subsumption_resolution,[],[f143,f93])).

fof(f93,plain,(
    ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f92,f89])).

fof(f89,plain,(
    k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(resolution,[],[f72,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f72,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f71,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f69,f66])).

fof(f66,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f64,f33])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f64,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f28,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f28,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f29,f37])).

fof(f29,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f92,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f90,f30])).

fof(f30,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f90,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f72,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f143,plain,(
    v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f141,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f141,plain,
    ( ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(sK1))
    | v1_xboole_0(k2_struct_0(sK1)) ),
    inference(resolution,[],[f131,f108])).

fof(f108,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK2))
      | ~ r1_tarski(X0,k2_struct_0(sK1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f99,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X0)
      | ~ r1_tarski(X2,X1)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f99,plain,(
    r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f98,f89])).

fof(f98,plain,(
    r1_xboole_0(u1_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f97,f77])).

fof(f77,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f67,f41])).

fof(f67,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f66,f38])).

fof(f97,plain,(
    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f96,f72])).

fof(f96,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f94,f67])).

fof(f94,plain,
    ( ~ l1_struct_0(sK2)
    | r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_struct_0(sK1) ),
    inference(resolution,[],[f88,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f88,plain,(
    r1_tsep_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f87,f67])).

fof(f87,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f83,f72])).

fof(f83,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | r1_tsep_1(sK1,sK2) ),
    inference(resolution,[],[f26,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f26,plain,
    ( r1_tsep_1(sK2,sK1)
    | r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f131,plain,(
    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(resolution,[],[f70,f71])).

fof(f70,plain,
    ( ~ l1_pre_topc(sK1)
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f68,f66])).

fof(f68,plain,
    ( ~ l1_pre_topc(sK1)
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f29,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 11:07:14 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.52  % (18757)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (18753)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (18757)Refutation not found, incomplete strategy% (18757)------------------------------
% 0.21/0.52  % (18757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18757)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18757)Memory used [KB]: 10618
% 0.21/0.52  % (18757)Time elapsed: 0.094 s
% 0.21/0.52  % (18757)------------------------------
% 0.21/0.52  % (18757)------------------------------
% 1.34/0.53  % (18756)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.34/0.53  % (18774)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.34/0.53  % (18765)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.34/0.53  % (18755)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.34/0.55  % (18756)Refutation found. Thanks to Tanya!
% 1.34/0.55  % SZS status Theorem for theBenchmark
% 1.34/0.55  % SZS output start Proof for theBenchmark
% 1.34/0.55  fof(f144,plain,(
% 1.34/0.55    $false),
% 1.34/0.55    inference(subsumption_resolution,[],[f143,f93])).
% 1.34/0.55  fof(f93,plain,(
% 1.34/0.55    ~v1_xboole_0(k2_struct_0(sK1))),
% 1.34/0.55    inference(forward_demodulation,[],[f92,f89])).
% 1.34/0.55  fof(f89,plain,(
% 1.34/0.55    k2_struct_0(sK1) = u1_struct_0(sK1)),
% 1.34/0.55    inference(resolution,[],[f72,f41])).
% 1.34/0.55  fof(f41,plain,(
% 1.34/0.55    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f24])).
% 1.34/0.55  fof(f24,plain,(
% 1.34/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.34/0.55    inference(ennf_transformation,[],[f3])).
% 1.34/0.55  fof(f3,axiom,(
% 1.34/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.34/0.55  fof(f72,plain,(
% 1.34/0.55    l1_struct_0(sK1)),
% 1.34/0.55    inference(resolution,[],[f71,f38])).
% 1.34/0.55  fof(f38,plain,(
% 1.34/0.55    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f19])).
% 1.34/0.55  fof(f19,plain,(
% 1.34/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.34/0.55    inference(ennf_transformation,[],[f5])).
% 1.34/0.55  fof(f5,axiom,(
% 1.34/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.34/0.55  fof(f71,plain,(
% 1.34/0.55    l1_pre_topc(sK1)),
% 1.34/0.55    inference(subsumption_resolution,[],[f69,f66])).
% 1.34/0.55  fof(f66,plain,(
% 1.34/0.55    l1_pre_topc(sK2)),
% 1.34/0.55    inference(subsumption_resolution,[],[f64,f33])).
% 1.34/0.55  fof(f33,plain,(
% 1.34/0.55    l1_pre_topc(sK0)),
% 1.34/0.55    inference(cnf_transformation,[],[f14])).
% 1.34/0.55  fof(f14,plain,(
% 1.34/0.55    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.34/0.55    inference(flattening,[],[f13])).
% 1.34/0.55  fof(f13,plain,(
% 1.34/0.55    ? [X0] : (? [X1] : (? [X2] : (((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.34/0.55    inference(ennf_transformation,[],[f12])).
% 1.34/0.55  fof(f12,plain,(
% 1.34/0.55    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 1.34/0.55    inference(pure_predicate_removal,[],[f11])).
% 1.34/0.55  fof(f11,negated_conjecture,(
% 1.34/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 1.34/0.55    inference(negated_conjecture,[],[f10])).
% 1.34/0.55  fof(f10,conjecture,(
% 1.34/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).
% 1.34/0.55  fof(f64,plain,(
% 1.34/0.55    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 1.34/0.55    inference(resolution,[],[f28,f37])).
% 1.34/0.55  fof(f37,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f18])).
% 1.34/0.55  fof(f18,plain,(
% 1.34/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.34/0.55    inference(ennf_transformation,[],[f6])).
% 1.34/0.55  fof(f6,axiom,(
% 1.34/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.34/0.55  fof(f28,plain,(
% 1.34/0.55    m1_pre_topc(sK2,sK0)),
% 1.34/0.55    inference(cnf_transformation,[],[f14])).
% 1.34/0.55  fof(f69,plain,(
% 1.34/0.55    ~l1_pre_topc(sK2) | l1_pre_topc(sK1)),
% 1.34/0.55    inference(resolution,[],[f29,f37])).
% 1.34/0.55  fof(f29,plain,(
% 1.34/0.55    m1_pre_topc(sK1,sK2)),
% 1.34/0.55    inference(cnf_transformation,[],[f14])).
% 1.34/0.55  fof(f92,plain,(
% 1.34/0.55    ~v1_xboole_0(u1_struct_0(sK1))),
% 1.34/0.55    inference(subsumption_resolution,[],[f90,f30])).
% 1.34/0.55  fof(f30,plain,(
% 1.34/0.55    ~v2_struct_0(sK1)),
% 1.34/0.55    inference(cnf_transformation,[],[f14])).
% 1.34/0.55  fof(f90,plain,(
% 1.34/0.55    v2_struct_0(sK1) | ~v1_xboole_0(u1_struct_0(sK1))),
% 1.34/0.55    inference(resolution,[],[f72,f39])).
% 1.34/0.55  fof(f39,plain,(
% 1.34/0.55    ( ! [X0] : (~l1_struct_0(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 1.34/0.55    inference(cnf_transformation,[],[f21])).
% 1.34/0.55  fof(f21,plain,(
% 1.34/0.55    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.34/0.55    inference(flattening,[],[f20])).
% 1.34/0.55  fof(f20,plain,(
% 1.34/0.55    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.34/0.55    inference(ennf_transformation,[],[f7])).
% 1.34/0.55  fof(f7,axiom,(
% 1.34/0.55    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.34/0.55  fof(f143,plain,(
% 1.34/0.55    v1_xboole_0(k2_struct_0(sK1))),
% 1.34/0.55    inference(subsumption_resolution,[],[f141,f56])).
% 1.34/0.55  fof(f56,plain,(
% 1.34/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.34/0.55    inference(equality_resolution,[],[f42])).
% 1.34/0.55  fof(f42,plain,(
% 1.34/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.34/0.55    inference(cnf_transformation,[],[f1])).
% 1.34/0.55  fof(f1,axiom,(
% 1.34/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.34/0.55  fof(f141,plain,(
% 1.34/0.55    ~r1_tarski(k2_struct_0(sK1),k2_struct_0(sK1)) | v1_xboole_0(k2_struct_0(sK1))),
% 1.34/0.55    inference(resolution,[],[f131,f108])).
% 1.34/0.55  fof(f108,plain,(
% 1.34/0.55    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK2)) | ~r1_tarski(X0,k2_struct_0(sK1)) | v1_xboole_0(X0)) )),
% 1.34/0.55    inference(resolution,[],[f99,f40])).
% 1.34/0.55  fof(f40,plain,(
% 1.34/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X0) | ~r1_tarski(X2,X1) | v1_xboole_0(X2)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f23])).
% 1.34/0.55  fof(f23,plain,(
% 1.34/0.55    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2))),
% 1.34/0.55    inference(flattening,[],[f22])).
% 1.34/0.55  fof(f22,plain,(
% 1.34/0.55    ! [X0,X1,X2] : ((~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0)) | v1_xboole_0(X2))),
% 1.34/0.55    inference(ennf_transformation,[],[f2])).
% 1.34/0.55  fof(f2,axiom,(
% 1.34/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).
% 1.34/0.55  fof(f99,plain,(
% 1.34/0.55    r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2))),
% 1.34/0.55    inference(forward_demodulation,[],[f98,f89])).
% 1.34/0.55  fof(f98,plain,(
% 1.34/0.55    r1_xboole_0(u1_struct_0(sK1),k2_struct_0(sK2))),
% 1.34/0.55    inference(forward_demodulation,[],[f97,f77])).
% 1.34/0.55  fof(f77,plain,(
% 1.34/0.55    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 1.34/0.55    inference(resolution,[],[f67,f41])).
% 1.34/0.55  fof(f67,plain,(
% 1.34/0.55    l1_struct_0(sK2)),
% 1.34/0.55    inference(resolution,[],[f66,f38])).
% 1.34/0.55  fof(f97,plain,(
% 1.34/0.55    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.34/0.55    inference(subsumption_resolution,[],[f96,f72])).
% 1.34/0.55  fof(f96,plain,(
% 1.34/0.55    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_struct_0(sK1)),
% 1.34/0.55    inference(subsumption_resolution,[],[f94,f67])).
% 1.34/0.55  fof(f94,plain,(
% 1.34/0.55    ~l1_struct_0(sK2) | r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_struct_0(sK1)),
% 1.34/0.55    inference(resolution,[],[f88,f36])).
% 1.34/0.55  fof(f36,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f17])).
% 1.34/0.55  fof(f17,plain,(
% 1.34/0.55    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.34/0.55    inference(ennf_transformation,[],[f8])).
% 1.34/0.55  fof(f8,axiom,(
% 1.34/0.55    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 1.34/0.55  fof(f88,plain,(
% 1.34/0.55    r1_tsep_1(sK1,sK2)),
% 1.34/0.55    inference(subsumption_resolution,[],[f87,f67])).
% 1.34/0.55  fof(f87,plain,(
% 1.34/0.55    r1_tsep_1(sK1,sK2) | ~l1_struct_0(sK2)),
% 1.34/0.55    inference(subsumption_resolution,[],[f83,f72])).
% 1.34/0.55  fof(f83,plain,(
% 1.34/0.55    r1_tsep_1(sK1,sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK2)),
% 1.34/0.55    inference(duplicate_literal_removal,[],[f82])).
% 1.34/0.55  fof(f82,plain,(
% 1.34/0.55    r1_tsep_1(sK1,sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK2) | r1_tsep_1(sK1,sK2)),
% 1.34/0.55    inference(resolution,[],[f26,f34])).
% 1.34/0.55  fof(f34,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X1,X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f16])).
% 1.34/0.55  fof(f16,plain,(
% 1.34/0.55    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.34/0.55    inference(flattening,[],[f15])).
% 1.34/0.55  fof(f15,plain,(
% 1.34/0.55    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 1.34/0.55    inference(ennf_transformation,[],[f9])).
% 1.34/0.55  fof(f9,axiom,(
% 1.34/0.55    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 1.34/0.55  fof(f26,plain,(
% 1.34/0.55    r1_tsep_1(sK2,sK1) | r1_tsep_1(sK1,sK2)),
% 1.34/0.55    inference(cnf_transformation,[],[f14])).
% 1.34/0.55  fof(f131,plain,(
% 1.34/0.55    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))),
% 1.34/0.55    inference(resolution,[],[f70,f71])).
% 1.34/0.55  fof(f70,plain,(
% 1.34/0.55    ~l1_pre_topc(sK1) | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))),
% 1.34/0.55    inference(subsumption_resolution,[],[f68,f66])).
% 1.34/0.55  fof(f68,plain,(
% 1.34/0.55    ~l1_pre_topc(sK1) | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) | ~l1_pre_topc(sK2)),
% 1.34/0.55    inference(resolution,[],[f29,f54])).
% 1.34/0.55  fof(f54,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f25])).
% 1.34/0.55  fof(f25,plain,(
% 1.34/0.55    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.34/0.55    inference(ennf_transformation,[],[f4])).
% 1.34/0.55  fof(f4,axiom,(
% 1.34/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).
% 1.34/0.55  % SZS output end Proof for theBenchmark
% 1.34/0.55  % (18756)------------------------------
% 1.34/0.55  % (18756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (18756)Termination reason: Refutation
% 1.34/0.55  
% 1.34/0.55  % (18756)Memory used [KB]: 6140
% 1.34/0.55  % (18756)Time elapsed: 0.116 s
% 1.34/0.55  % (18756)------------------------------
% 1.34/0.55  % (18756)------------------------------
% 1.49/0.55  % (18750)Success in time 0.192 s
%------------------------------------------------------------------------------

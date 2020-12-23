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
% DateTime   : Thu Dec  3 13:10:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 (1112 expanded)
%              Number of leaves         :   10 ( 196 expanded)
%              Depth                    :   36
%              Number of atoms          :  535 (8244 expanded)
%              Number of equality atoms :   39 ( 121 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (7118)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f280,plain,(
    $false ),
    inference(subsumption_resolution,[],[f271,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f271,plain,(
    ~ r1_tarski(k1_xboole_0,k1_funct_1(sK1,u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f190,f265])).

fof(f265,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f264,f241])).

fof(f241,plain,(
    m1_orders_2(sK2,sK0,sK2) ),
    inference(subsumption_resolution,[],[f240,f56])).

fof(f56,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f240,plain,
    ( r2_xboole_0(sK2,sK2)
    | m1_orders_2(sK2,sK0,sK2) ),
    inference(forward_demodulation,[],[f226,f225])).

fof(f225,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f224,f183])).

fof(f183,plain,
    ( r2_xboole_0(sK2,sK3)
    | sK2 = sK3 ),
    inference(resolution,[],[f180,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f180,plain,(
    r1_tarski(sK2,sK3) ),
    inference(subsumption_resolution,[],[f179,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f179,plain,
    ( r2_xboole_0(sK2,sK3)
    | r1_tarski(sK2,sK3) ),
    inference(subsumption_resolution,[],[f178,f127])).

fof(f127,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f126,f35])).

fof(f35,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f13])).

% (7129)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f126,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f125,f40])).

fof(f40,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f125,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f124,f39])).

fof(f39,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f124,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f123,f38])).

fof(f38,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f123,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f122,f37])).

fof(f37,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f122,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f103,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f103,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f33,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f33,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f178,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK3) ),
    inference(subsumption_resolution,[],[f177,f40])).

fof(f177,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK3) ),
    inference(subsumption_resolution,[],[f176,f39])).

fof(f176,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK3) ),
    inference(subsumption_resolution,[],[f175,f38])).

fof(f175,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK3) ),
    inference(subsumption_resolution,[],[f174,f37])).

fof(f174,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK3) ),
    inference(subsumption_resolution,[],[f171,f36])).

fof(f171,plain,
    ( r2_xboole_0(sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK3) ),
    inference(resolution,[],[f31,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | r1_tarski(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f31,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f224,plain,
    ( sK2 = sK3
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f217,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f217,plain,
    ( sK2 = sK3
    | r1_tarski(sK3,sK2)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f216,f32])).

fof(f32,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f216,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3
    | r1_tarski(sK3,sK2) ),
    inference(subsumption_resolution,[],[f215,f158])).

fof(f158,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f157,f35])).

fof(f157,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f156,f40])).

fof(f156,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f155,f39])).

% (7113)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f155,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f154,f38])).

fof(f154,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f153,f37])).

fof(f153,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f134,f36])).

fof(f134,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f34,f49])).

fof(f34,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f215,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK3,sK2) ),
    inference(subsumption_resolution,[],[f214,f40])).

fof(f214,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK3,sK2) ),
    inference(subsumption_resolution,[],[f213,f39])).

fof(f213,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK3,sK2) ),
    inference(subsumption_resolution,[],[f212,f38])).

fof(f212,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK3,sK2) ),
    inference(subsumption_resolution,[],[f211,f37])).

fof(f211,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK3,sK2) ),
    inference(subsumption_resolution,[],[f208,f36])).

fof(f208,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK3,sK2) ),
    inference(resolution,[],[f203,f45])).

fof(f203,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3 ),
    inference(resolution,[],[f115,f34])).

fof(f115,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | sK3 = X0
      | m1_orders_2(X0,sK0,sK3)
      | m1_orders_2(sK3,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f114,f35])).

fof(f114,plain,(
    ! [X0] :
      ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X0,sK0,sK1)
      | sK3 = X0
      | m1_orders_2(X0,sK0,sK3)
      | m1_orders_2(sK3,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f113,f40])).

fof(f113,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X0,sK0,sK1)
      | sK3 = X0
      | m1_orders_2(X0,sK0,sK3)
      | m1_orders_2(sK3,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f112,f39])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X0,sK0,sK1)
      | sK3 = X0
      | m1_orders_2(X0,sK0,sK3)
      | m1_orders_2(sK3,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f111,f38])).

fof(f111,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X0,sK0,sK1)
      | sK3 = X0
      | m1_orders_2(X0,sK0,sK3)
      | m1_orders_2(sK3,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f110,f37])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X0,sK0,sK1)
      | sK3 = X0
      | m1_orders_2(X0,sK0,sK3)
      | m1_orders_2(sK3,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f98,f36])).

fof(f98,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X0,sK0,sK1)
      | sK3 = X0
      | m1_orders_2(X0,sK0,sK3)
      | m1_orders_2(sK3,sK0,X0) ) ),
    inference(resolution,[],[f33,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m2_orders_2(X3,X0,X1)
      | X2 = X3
      | m1_orders_2(X3,X0,X2)
      | m1_orders_2(X2,X0,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f226,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | r2_xboole_0(sK2,sK3) ),
    inference(backward_demodulation,[],[f31,f225])).

fof(f264,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,sK2) ),
    inference(subsumption_resolution,[],[f263,f158])).

fof(f263,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,sK2) ),
    inference(subsumption_resolution,[],[f262,f40])).

fof(f262,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,sK2) ),
    inference(subsumption_resolution,[],[f261,f39])).

fof(f261,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,sK2) ),
    inference(subsumption_resolution,[],[f260,f38])).

fof(f260,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,sK2) ),
    inference(subsumption_resolution,[],[f259,f37])).

fof(f259,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,sK2) ),
    inference(subsumption_resolution,[],[f258,f36])).

fof(f258,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,sK2) ),
    inference(resolution,[],[f241,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X1,X0,X2)
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f190,plain,(
    ~ r1_tarski(sK2,k1_funct_1(sK1,u1_struct_0(sK0))) ),
    inference(resolution,[],[f140,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f140,plain,(
    r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2) ),
    inference(subsumption_resolution,[],[f139,f35])).

fof(f139,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2) ),
    inference(subsumption_resolution,[],[f138,f40])).

fof(f138,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2) ),
    inference(subsumption_resolution,[],[f137,f39])).

fof(f137,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2) ),
    inference(subsumption_resolution,[],[f136,f38])).

fof(f136,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2) ),
    inference(subsumption_resolution,[],[f135,f37])).

% (7117)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f135,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2) ),
    inference(subsumption_resolution,[],[f128,f36])).

fof(f128,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2) ),
    inference(resolution,[],[f34,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
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
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (7126)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (7115)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (7127)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (7126)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  % (7118)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f271,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.49  fof(f271,plain,(
% 0.21/0.49    ~r1_tarski(k1_xboole_0,k1_funct_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.49    inference(backward_demodulation,[],[f190,f265])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    k1_xboole_0 = sK2),
% 0.21/0.49    inference(subsumption_resolution,[],[f264,f241])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    m1_orders_2(sK2,sK0,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f240,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    r2_xboole_0(sK2,sK2) | m1_orders_2(sK2,sK0,sK2)),
% 0.21/0.49    inference(forward_demodulation,[],[f226,f225])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    sK2 = sK3),
% 0.21/0.49    inference(subsumption_resolution,[],[f224,f183])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    r2_xboole_0(sK2,sK3) | sK2 = sK3),
% 0.21/0.49    inference(resolution,[],[f180,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    r1_tarski(sK2,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f179,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    r2_xboole_0(sK2,sK3) | r1_tarski(sK2,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f178,f127])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f126,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  % (7129)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  fof(f13,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f12])).
% 0.21/0.49  fof(f12,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f125,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    l1_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f124,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    v5_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f123,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    v4_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f122,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    v3_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f103,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(resolution,[],[f33,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    m2_orders_2(sK3,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    r2_xboole_0(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f177,f40])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    r2_xboole_0(sK2,sK3) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f176,f39])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    r2_xboole_0(sK2,sK3) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f175,f38])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    r2_xboole_0(sK2,sK3) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f174,f37])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    r2_xboole_0(sK2,sK3) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f171,f36])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    r2_xboole_0(sK2,sK3) | v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,sK3)),
% 0.21/0.49    inference(resolution,[],[f31,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    sK2 = sK3 | ~r2_xboole_0(sK2,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f217,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    sK2 = sK3 | r1_tarski(sK3,sK2) | ~r2_xboole_0(sK2,sK3)),
% 0.21/0.49    inference(resolution,[],[f216,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    m1_orders_2(sK2,sK0,sK3) | sK2 = sK3 | r1_tarski(sK3,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f215,f158])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f157,f35])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f156,f40])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f155,f39])).
% 0.21/0.49  % (7113)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f154,f38])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f153,f37])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f134,f36])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(resolution,[],[f34,f49])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    m2_orders_2(sK2,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    m1_orders_2(sK2,sK0,sK3) | sK2 = sK3 | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK3,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f214,f40])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    m1_orders_2(sK2,sK0,sK3) | sK2 = sK3 | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK3,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f213,f39])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    m1_orders_2(sK2,sK0,sK3) | sK2 = sK3 | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK3,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f212,f38])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    m1_orders_2(sK2,sK0,sK3) | sK2 = sK3 | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK3,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f211,f37])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    m1_orders_2(sK2,sK0,sK3) | sK2 = sK3 | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK3,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f208,f36])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    m1_orders_2(sK2,sK0,sK3) | sK2 = sK3 | v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK3,sK2)),
% 0.21/0.49    inference(resolution,[],[f203,f45])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    m1_orders_2(sK3,sK0,sK2) | m1_orders_2(sK2,sK0,sK3) | sK2 = sK3),
% 0.21/0.49    inference(resolution,[],[f115,f34])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK3 = X0 | m1_orders_2(X0,sK0,sK3) | m1_orders_2(sK3,sK0,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f114,f35])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X0,sK0,sK1) | sK3 = X0 | m1_orders_2(X0,sK0,sK3) | m1_orders_2(sK3,sK0,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f113,f40])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X0,sK0,sK1) | sK3 = X0 | m1_orders_2(X0,sK0,sK3) | m1_orders_2(sK3,sK0,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f112,f39])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X0] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X0,sK0,sK1) | sK3 = X0 | m1_orders_2(X0,sK0,sK3) | m1_orders_2(sK3,sK0,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f111,f38])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X0,sK0,sK1) | sK3 = X0 | m1_orders_2(X0,sK0,sK3) | m1_orders_2(sK3,sK0,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f110,f37])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X0,sK0,sK1) | sK3 = X0 | m1_orders_2(X0,sK0,sK3) | m1_orders_2(sK3,sK0,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f98,f36])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X0] : (v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X0,sK0,sK1) | sK3 = X0 | m1_orders_2(X0,sK0,sK3) | m1_orders_2(sK3,sK0,X0)) )),
% 0.21/0.49    inference(resolution,[],[f33,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m2_orders_2(X3,X0,X1) | X2 = X3 | m1_orders_2(X3,X0,X2) | m1_orders_2(X2,X0,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    m1_orders_2(sK2,sK0,sK2) | r2_xboole_0(sK2,sK3)),
% 0.21/0.49    inference(backward_demodulation,[],[f31,f225])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | ~m1_orders_2(sK2,sK0,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f263,f158])).
% 0.21/0.49  fof(f263,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | ~m1_orders_2(sK2,sK0,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f262,f40])).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | ~m1_orders_2(sK2,sK0,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f261,f39])).
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | ~m1_orders_2(sK2,sK0,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f260,f38])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | ~m1_orders_2(sK2,sK0,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f259,f37])).
% 0.21/0.49  fof(f259,plain,(
% 0.21/0.49    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | ~m1_orders_2(sK2,sK0,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f258,f36])).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | ~m1_orders_2(sK2,sK0,sK2)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f252])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | ~m1_orders_2(sK2,sK0,sK2)),
% 0.21/0.49    inference(resolution,[],[f241,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | ~m1_orders_2(X1,X0,X2) | ~m1_orders_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    ~r1_tarski(sK2,k1_funct_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.49    inference(resolution,[],[f140,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f139,f35])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f138,f40])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f137,f39])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f136,f38])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f135,f37])).
% 0.21/0.49  % (7117)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f128,f36])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2)),
% 0.21/0.49    inference(resolution,[],[f34,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (7126)------------------------------
% 0.21/0.49  % (7126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7126)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (7126)Memory used [KB]: 1663
% 0.21/0.49  % (7126)Time elapsed: 0.063 s
% 0.21/0.49  % (7126)------------------------------
% 0.21/0.49  % (7126)------------------------------
% 0.21/0.49  % (7113)Refutation not found, incomplete strategy% (7113)------------------------------
% 0.21/0.49  % (7113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7112)Success in time 0.135 s
%------------------------------------------------------------------------------

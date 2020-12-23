%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 191 expanded)
%              Number of leaves         :   11 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  197 ( 840 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(subsumption_resolution,[],[f89,f28])).

fof(f28,plain,(
    ~ r3_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
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
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) )
           => r3_orders_1(u1_orders_2(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X1,X0) )
         => r3_orders_1(u1_orders_2(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_orders_2)).

fof(f89,plain,(
    r3_orders_1(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f88,f63])).

fof(f63,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f62,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f62,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f34,f33])).

fof(f33,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f88,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | r3_orders_1(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f87,f68])).

fof(f68,plain,(
    r4_relat_2(u1_orders_2(sK0),sK1) ),
    inference(resolution,[],[f67,f54])).

fof(f54,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f50,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | r4_relat_2(u1_orders_2(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f66,f63])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(u1_orders_2(sK0))
      | ~ r1_tarski(X0,u1_struct_0(sK0))
      | r4_relat_2(u1_orders_2(sK0),X0) ) ),
    inference(resolution,[],[f51,f57])).

fof(f57,plain,(
    r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f56,f33])).

fof(f56,plain,
    ( r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f36,f32])).

fof(f32,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v5_orders_2(X0)
      | r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X0)
      | r4_relat_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r4_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r4_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

% (2448)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r4_relat_2(X2,X0) )
       => r4_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_orders_1)).

fof(f87,plain,
    ( ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | r3_orders_1(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f86,f73])).

fof(f73,plain,(
    r8_relat_2(u1_orders_2(sK0),sK1) ),
    inference(resolution,[],[f72,f54])).

fof(f72,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | r8_relat_2(u1_orders_2(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f71,f63])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_relat_1(u1_orders_2(sK0))
      | ~ r1_tarski(X0,u1_struct_0(sK0))
      | r8_relat_2(u1_orders_2(sK0),X0) ) ),
    inference(resolution,[],[f52,f60])).

fof(f60,plain,(
    r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f59,f33])).

fof(f59,plain,
    ( r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f38,f31])).

fof(f31,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v4_orders_2(X0)
      | r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_2)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X0)
      | r8_relat_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r8_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r8_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r8_relat_2(X2,X0) )
       => r8_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_orders_1)).

fof(f86,plain,
    ( ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | r3_orders_1(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f85,f83])).

fof(f83,plain,(
    r1_relat_2(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f81,f63])).

fof(f81,plain,
    ( r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f79,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r7_relat_2(X1,X0)
      | r1_relat_2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_orders_1)).

fof(f79,plain,(
    r7_relat_2(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f78,f26])).

fof(f26,plain,(
    v6_orders_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f78,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ v6_orders_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f77,f33])).

fof(f77,plain,
    ( ~ l1_orders_2(sK0)
    | r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ v6_orders_2(sK1,sK0) ),
    inference(resolution,[],[f40,f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r7_relat_2(u1_orders_2(X0),X1)
      | ~ v6_orders_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

fof(f85,plain,
    ( ~ r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | r3_orders_1(u1_orders_2(sK0),sK1) ),
    inference(resolution,[],[f45,f82])).

fof(f82,plain,(
    r6_relat_2(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f80,f63])).

fof(f80,plain,
    ( r6_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f79,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r7_relat_2(X1,X0)
      | r6_relat_2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r6_relat_2(X0,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ v1_relat_1(X0)
      | r3_orders_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_orders_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:07:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.42  % (2447)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.19/0.44  % (2440)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.19/0.44  % (2440)Refutation found. Thanks to Tanya!
% 0.19/0.44  % SZS status Theorem for theBenchmark
% 0.19/0.44  % SZS output start Proof for theBenchmark
% 0.19/0.44  fof(f90,plain,(
% 0.19/0.44    $false),
% 0.19/0.44    inference(subsumption_resolution,[],[f89,f28])).
% 0.19/0.44  fof(f28,plain,(
% 0.19/0.44    ~r3_orders_1(u1_orders_2(sK0),sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f14])).
% 0.19/0.44  fof(f14,plain,(
% 0.19/0.44    ? [X0] : (? [X1] : (~r3_orders_1(u1_orders_2(X0),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.19/0.44    inference(flattening,[],[f13])).
% 0.19/0.44  fof(f13,plain,(
% 0.19/0.44    ? [X0] : (? [X1] : (~r3_orders_1(u1_orders_2(X0),X1) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.19/0.44    inference(ennf_transformation,[],[f12])).
% 0.19/0.44  fof(f12,negated_conjecture,(
% 0.19/0.44    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)) => r3_orders_1(u1_orders_2(X0),X1)))),
% 0.19/0.44    inference(negated_conjecture,[],[f11])).
% 0.19/0.44  fof(f11,conjecture,(
% 0.19/0.44    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)) => r3_orders_1(u1_orders_2(X0),X1)))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_orders_2)).
% 0.19/0.44  fof(f89,plain,(
% 0.19/0.44    r3_orders_1(u1_orders_2(sK0),sK1)),
% 0.19/0.44    inference(subsumption_resolution,[],[f88,f63])).
% 0.19/0.44  fof(f63,plain,(
% 0.19/0.44    v1_relat_1(u1_orders_2(sK0))),
% 0.19/0.44    inference(resolution,[],[f62,f53])).
% 0.19/0.44  fof(f53,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f25])).
% 0.19/0.44  fof(f25,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.44    inference(ennf_transformation,[],[f2])).
% 0.19/0.44  fof(f2,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.44  fof(f62,plain,(
% 0.19/0.44    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.19/0.44    inference(resolution,[],[f34,f33])).
% 0.19/0.44  fof(f33,plain,(
% 0.19/0.44    l1_orders_2(sK0)),
% 0.19/0.44    inference(cnf_transformation,[],[f14])).
% 0.19/0.44  fof(f34,plain,(
% 0.19/0.44    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f15])).
% 0.19/0.44  fof(f15,plain,(
% 0.19/0.44    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.19/0.44    inference(ennf_transformation,[],[f7])).
% 0.19/0.44  fof(f7,axiom,(
% 0.19/0.44    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.19/0.44  fof(f88,plain,(
% 0.19/0.44    ~v1_relat_1(u1_orders_2(sK0)) | r3_orders_1(u1_orders_2(sK0),sK1)),
% 0.19/0.44    inference(subsumption_resolution,[],[f87,f68])).
% 0.19/0.44  fof(f68,plain,(
% 0.19/0.44    r4_relat_2(u1_orders_2(sK0),sK1)),
% 0.19/0.44    inference(resolution,[],[f67,f54])).
% 0.19/0.44  fof(f54,plain,(
% 0.19/0.44    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.19/0.44    inference(resolution,[],[f50,f27])).
% 0.19/0.44  fof(f27,plain,(
% 0.19/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.44    inference(cnf_transformation,[],[f14])).
% 0.19/0.44  fof(f50,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f1])).
% 0.19/0.44  fof(f1,axiom,(
% 0.19/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.44  fof(f67,plain,(
% 0.19/0.44    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | r4_relat_2(u1_orders_2(sK0),X0)) )),
% 0.19/0.44    inference(subsumption_resolution,[],[f66,f63])).
% 0.19/0.44  fof(f66,plain,(
% 0.19/0.44    ( ! [X0] : (~v1_relat_1(u1_orders_2(sK0)) | ~r1_tarski(X0,u1_struct_0(sK0)) | r4_relat_2(u1_orders_2(sK0),X0)) )),
% 0.19/0.44    inference(resolution,[],[f51,f57])).
% 0.19/0.44  fof(f57,plain,(
% 0.19/0.44    r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))),
% 0.19/0.44    inference(subsumption_resolution,[],[f56,f33])).
% 0.19/0.44  fof(f56,plain,(
% 0.19/0.44    r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.19/0.44    inference(resolution,[],[f36,f32])).
% 0.19/0.44  fof(f32,plain,(
% 0.19/0.44    v5_orders_2(sK0)),
% 0.19/0.44    inference(cnf_transformation,[],[f14])).
% 0.19/0.44  fof(f36,plain,(
% 0.19/0.44    ( ! [X0] : (~v5_orders_2(X0) | r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f16])).
% 0.19/0.44  fof(f16,plain,(
% 0.19/0.44    ! [X0] : ((v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.19/0.44    inference(ennf_transformation,[],[f5])).
% 0.19/0.44  fof(f5,axiom,(
% 0.19/0.44    ! [X0] : (l1_orders_2(X0) => (v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).
% 0.19/0.44  fof(f51,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~r4_relat_2(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X1,X0) | r4_relat_2(X2,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f22])).
% 0.19/0.44  fof(f22,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (r4_relat_2(X2,X1) | ~r1_tarski(X1,X0) | ~r4_relat_2(X2,X0) | ~v1_relat_1(X2))),
% 0.19/0.44    inference(flattening,[],[f21])).
% 0.19/0.44  fof(f21,plain,(
% 0.19/0.44    ! [X0,X1,X2] : ((r4_relat_2(X2,X1) | (~r1_tarski(X1,X0) | ~r4_relat_2(X2,X0))) | ~v1_relat_1(X2))),
% 0.19/0.44    inference(ennf_transformation,[],[f9])).
% 0.19/0.46  % (2448)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.19/0.46  fof(f9,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(X1,X0) & r4_relat_2(X2,X0)) => r4_relat_2(X2,X1)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_orders_1)).
% 0.19/0.46  fof(f87,plain,(
% 0.19/0.46    ~r4_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0)) | r3_orders_1(u1_orders_2(sK0),sK1)),
% 0.19/0.46    inference(subsumption_resolution,[],[f86,f73])).
% 0.19/0.46  fof(f73,plain,(
% 0.19/0.46    r8_relat_2(u1_orders_2(sK0),sK1)),
% 0.19/0.46    inference(resolution,[],[f72,f54])).
% 0.19/0.46  fof(f72,plain,(
% 0.19/0.46    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | r8_relat_2(u1_orders_2(sK0),X0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f71,f63])).
% 0.19/0.46  fof(f71,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_relat_1(u1_orders_2(sK0)) | ~r1_tarski(X0,u1_struct_0(sK0)) | r8_relat_2(u1_orders_2(sK0),X0)) )),
% 0.19/0.46    inference(resolution,[],[f52,f60])).
% 0.19/0.46  fof(f60,plain,(
% 0.19/0.46    r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))),
% 0.19/0.46    inference(subsumption_resolution,[],[f59,f33])).
% 0.19/0.46  fof(f59,plain,(
% 0.19/0.46    r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.19/0.46    inference(resolution,[],[f38,f31])).
% 0.19/0.46  fof(f31,plain,(
% 0.19/0.46    v4_orders_2(sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f14])).
% 0.19/0.46  fof(f38,plain,(
% 0.19/0.46    ( ! [X0] : (~v4_orders_2(X0) | r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f17])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ! [X0] : ((v4_orders_2(X0) <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0] : (l1_orders_2(X0) => (v4_orders_2(X0) <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_2)).
% 0.19/0.46  fof(f52,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r8_relat_2(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X1,X0) | r8_relat_2(X2,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f24])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (r8_relat_2(X2,X1) | ~r1_tarski(X1,X0) | ~r8_relat_2(X2,X0) | ~v1_relat_1(X2))),
% 0.19/0.46    inference(flattening,[],[f23])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((r8_relat_2(X2,X1) | (~r1_tarski(X1,X0) | ~r8_relat_2(X2,X0))) | ~v1_relat_1(X2))),
% 0.19/0.46    inference(ennf_transformation,[],[f10])).
% 0.19/0.46  fof(f10,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(X1,X0) & r8_relat_2(X2,X0)) => r8_relat_2(X2,X1)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_orders_1)).
% 0.19/0.46  fof(f86,plain,(
% 0.19/0.46    ~r8_relat_2(u1_orders_2(sK0),sK1) | ~r4_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0)) | r3_orders_1(u1_orders_2(sK0),sK1)),
% 0.19/0.46    inference(subsumption_resolution,[],[f85,f83])).
% 0.19/0.46  fof(f83,plain,(
% 0.19/0.46    r1_relat_2(u1_orders_2(sK0),sK1)),
% 0.19/0.46    inference(subsumption_resolution,[],[f81,f63])).
% 0.19/0.46  fof(f81,plain,(
% 0.19/0.46    r1_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0))),
% 0.19/0.46    inference(resolution,[],[f79,f46])).
% 0.19/0.46  fof(f46,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r7_relat_2(X1,X0) | r1_relat_2(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f20])).
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    ! [X0,X1] : ((r7_relat_2(X1,X0) <=> (r6_relat_2(X1,X0) & r1_relat_2(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.46    inference(ennf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,axiom,(
% 0.19/0.46    ! [X0,X1] : (v1_relat_1(X1) => (r7_relat_2(X1,X0) <=> (r6_relat_2(X1,X0) & r1_relat_2(X1,X0))))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_orders_1)).
% 0.19/0.46  fof(f79,plain,(
% 0.19/0.46    r7_relat_2(u1_orders_2(sK0),sK1)),
% 0.19/0.46    inference(subsumption_resolution,[],[f78,f26])).
% 0.19/0.46  fof(f26,plain,(
% 0.19/0.46    v6_orders_2(sK1,sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f14])).
% 0.19/0.46  fof(f78,plain,(
% 0.19/0.46    r7_relat_2(u1_orders_2(sK0),sK1) | ~v6_orders_2(sK1,sK0)),
% 0.19/0.46    inference(subsumption_resolution,[],[f77,f33])).
% 0.19/0.46  fof(f77,plain,(
% 0.19/0.46    ~l1_orders_2(sK0) | r7_relat_2(u1_orders_2(sK0),sK1) | ~v6_orders_2(sK1,sK0)),
% 0.19/0.46    inference(resolution,[],[f40,f27])).
% 0.19/0.46  fof(f40,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | r7_relat_2(u1_orders_2(X0),X1) | ~v6_orders_2(X1,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f18])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : ((v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1))))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).
% 0.19/0.46  fof(f85,plain,(
% 0.19/0.46    ~r1_relat_2(u1_orders_2(sK0),sK1) | ~r8_relat_2(u1_orders_2(sK0),sK1) | ~r4_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0)) | r3_orders_1(u1_orders_2(sK0),sK1)),
% 0.19/0.46    inference(resolution,[],[f45,f82])).
% 0.19/0.46  fof(f82,plain,(
% 0.19/0.46    r6_relat_2(u1_orders_2(sK0),sK1)),
% 0.19/0.46    inference(subsumption_resolution,[],[f80,f63])).
% 0.19/0.46  fof(f80,plain,(
% 0.19/0.46    r6_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0))),
% 0.19/0.46    inference(resolution,[],[f79,f47])).
% 0.19/0.46  fof(f47,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r7_relat_2(X1,X0) | r6_relat_2(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f20])).
% 0.19/0.46  fof(f45,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r6_relat_2(X0,X1) | ~r1_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~v1_relat_1(X0) | r3_orders_1(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f19])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (r3_orders_1(X0,X1) <=> (r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f6])).
% 0.19/0.46  fof(f6,axiom,(
% 0.19/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r3_orders_1(X0,X1) <=> (r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_orders_1)).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (2440)------------------------------
% 0.19/0.46  % (2440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (2440)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (2440)Memory used [KB]: 5373
% 0.19/0.46  % (2440)Time elapsed: 0.047 s
% 0.19/0.46  % (2440)------------------------------
% 0.19/0.46  % (2440)------------------------------
% 0.19/0.46  % (2433)Success in time 0.107 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:50 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 192 expanded)
%              Number of leaves         :   15 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  159 ( 376 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1263,plain,(
    $false ),
    inference(resolution,[],[f390,f280])).

fof(f280,plain,(
    ! [X1] : r1_tarski(k7_relat_1(sK3,X1),k2_zfmisc_1(sK0,sK2)) ),
    inference(resolution,[],[f244,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3)
      | r1_tarski(X0,k2_zfmisc_1(sK0,sK2)) ) ),
    inference(resolution,[],[f61,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f61,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(resolution,[],[f37,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

fof(f244,plain,(
    ! [X15] : r1_tarski(k7_relat_1(sK3,X15),sK3) ),
    inference(backward_demodulation,[],[f219,f243])).

fof(f243,plain,(
    ! [X14] : k7_relat_1(sK3,X14) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X14))) ),
    inference(forward_demodulation,[],[f239,f110])).

fof(f110,plain,(
    ! [X10] : k7_relat_1(sK3,X10) = k7_relat_1(k7_relat_1(sK3,X10),k1_relat_1(k7_relat_1(sK3,X10))) ),
    inference(resolution,[],[f72,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f72,plain,(
    ! [X10] : v1_relat_1(k7_relat_1(sK3,X10)) ),
    inference(resolution,[],[f63,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f63,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f60,f46])).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f60,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f239,plain,(
    ! [X14] : k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X14))) = k7_relat_1(k7_relat_1(sK3,X14),k1_relat_1(k7_relat_1(sK3,X14))) ),
    inference(resolution,[],[f66,f71])).

fof(f71,plain,(
    ! [X9] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X9)),X9) ),
    inference(resolution,[],[f63,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f66,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | k7_relat_1(k7_relat_1(sK3,X4),X3) = k7_relat_1(sK3,X3) ) ),
    inference(resolution,[],[f63,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

fof(f219,plain,(
    ! [X15] : r1_tarski(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X15))),sK3) ),
    inference(forward_demodulation,[],[f216,f68])).

fof(f68,plain,(
    sK3 = k7_relat_1(sK3,k1_relat_1(sK3)) ),
    inference(resolution,[],[f63,f49])).

fof(f216,plain,(
    ! [X15] : r1_tarski(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X15))),k7_relat_1(sK3,k1_relat_1(sK3))) ),
    inference(resolution,[],[f69,f70])).

fof(f70,plain,(
    ! [X8] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X8)),k1_relat_1(sK3)) ),
    inference(resolution,[],[f63,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

fof(f69,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | r1_tarski(k7_relat_1(sK3,X6),k7_relat_1(sK3,X7)) ) ),
    inference(resolution,[],[f63,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).

fof(f390,plain,(
    ! [X1] : ~ r1_tarski(k7_relat_1(sK3,sK1),k2_zfmisc_1(X1,sK2)) ),
    inference(resolution,[],[f140,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f140,plain,(
    ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ),
    inference(resolution,[],[f95,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f95,plain,(
    ~ v5_relat_1(k7_relat_1(sK3,sK1),sK2) ),
    inference(subsumption_resolution,[],[f91,f72])).

fof(f91,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ v5_relat_1(k7_relat_1(sK3,sK1),sK2) ),
    inference(resolution,[],[f79,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f79,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) ),
    inference(subsumption_resolution,[],[f78,f71])).

fof(f78,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) ),
    inference(subsumption_resolution,[],[f75,f72])).

fof(f75,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) ),
    inference(resolution,[],[f62,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f62,plain,(
    ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(backward_demodulation,[],[f38,f59])).

fof(f59,plain,(
    ! [X0] : k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(resolution,[],[f37,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f38,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:21:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (18424)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.47  % (18430)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.48  % (18424)Refutation not found, incomplete strategy% (18424)------------------------------
% 0.21/0.48  % (18424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18424)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (18424)Memory used [KB]: 10618
% 0.21/0.48  % (18424)Time elapsed: 0.064 s
% 0.21/0.48  % (18424)------------------------------
% 0.21/0.48  % (18424)------------------------------
% 0.21/0.49  % (18431)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.49  % (18437)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (18433)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.50  % (18421)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (18439)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.50  % (18428)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.50  % (18420)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (18428)Refutation not found, incomplete strategy% (18428)------------------------------
% 0.21/0.50  % (18428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (18428)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (18428)Memory used [KB]: 10618
% 0.21/0.50  % (18428)Time elapsed: 0.080 s
% 0.21/0.50  % (18428)------------------------------
% 0.21/0.50  % (18428)------------------------------
% 0.21/0.51  % (18436)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (18422)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (18419)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (18429)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  % (18440)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.52  % (18423)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.52  % (18434)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.52  % (18418)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.53  % (18425)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (18426)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.38/0.53  % (18426)Refutation not found, incomplete strategy% (18426)------------------------------
% 1.38/0.53  % (18426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (18426)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (18426)Memory used [KB]: 10490
% 1.38/0.53  % (18426)Time elapsed: 0.122 s
% 1.38/0.53  % (18426)------------------------------
% 1.38/0.53  % (18426)------------------------------
% 1.38/0.53  % (18435)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.38/0.53  % (18432)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.38/0.54  % (18438)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.38/0.54  % (18441)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.49/0.55  % (18427)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.49/0.55  % (18439)Refutation found. Thanks to Tanya!
% 1.49/0.55  % SZS status Theorem for theBenchmark
% 1.49/0.55  % SZS output start Proof for theBenchmark
% 1.49/0.55  fof(f1263,plain,(
% 1.49/0.55    $false),
% 1.49/0.55    inference(resolution,[],[f390,f280])).
% 1.49/0.55  fof(f280,plain,(
% 1.49/0.55    ( ! [X1] : (r1_tarski(k7_relat_1(sK3,X1),k2_zfmisc_1(sK0,sK2))) )),
% 1.49/0.55    inference(resolution,[],[f244,f86])).
% 1.49/0.55  fof(f86,plain,(
% 1.49/0.55    ( ! [X0] : (~r1_tarski(X0,sK3) | r1_tarski(X0,k2_zfmisc_1(sK0,sK2))) )),
% 1.49/0.55    inference(resolution,[],[f61,f56])).
% 1.49/0.55  fof(f56,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f36])).
% 1.49/0.55  fof(f36,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.49/0.55    inference(flattening,[],[f35])).
% 1.49/0.55  fof(f35,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.49/0.55    inference(ennf_transformation,[],[f1])).
% 1.49/0.55  fof(f1,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.49/0.55  fof(f61,plain,(
% 1.49/0.55    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))),
% 1.49/0.55    inference(resolution,[],[f37,f44])).
% 1.49/0.55  fof(f44,plain,(
% 1.49/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f2])).
% 1.49/0.55  fof(f2,axiom,(
% 1.49/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.49/0.55  fof(f37,plain,(
% 1.49/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.49/0.55    inference(cnf_transformation,[],[f18])).
% 1.49/0.55  fof(f18,plain,(
% 1.49/0.55    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.49/0.55    inference(ennf_transformation,[],[f17])).
% 1.49/0.55  fof(f17,negated_conjecture,(
% 1.49/0.55    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.49/0.55    inference(negated_conjecture,[],[f16])).
% 1.49/0.55  fof(f16,conjecture,(
% 1.49/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).
% 1.49/0.55  fof(f244,plain,(
% 1.49/0.55    ( ! [X15] : (r1_tarski(k7_relat_1(sK3,X15),sK3)) )),
% 1.49/0.55    inference(backward_demodulation,[],[f219,f243])).
% 1.49/0.55  fof(f243,plain,(
% 1.49/0.55    ( ! [X14] : (k7_relat_1(sK3,X14) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X14)))) )),
% 1.49/0.55    inference(forward_demodulation,[],[f239,f110])).
% 1.49/0.55  fof(f110,plain,(
% 1.49/0.55    ( ! [X10] : (k7_relat_1(sK3,X10) = k7_relat_1(k7_relat_1(sK3,X10),k1_relat_1(k7_relat_1(sK3,X10)))) )),
% 1.49/0.55    inference(resolution,[],[f72,f49])).
% 1.49/0.55  fof(f49,plain,(
% 1.49/0.55    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 1.49/0.55    inference(cnf_transformation,[],[f28])).
% 1.49/0.55  fof(f28,plain,(
% 1.49/0.55    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f12])).
% 1.49/0.55  fof(f12,axiom,(
% 1.49/0.55    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 1.49/0.55  fof(f72,plain,(
% 1.49/0.55    ( ! [X10] : (v1_relat_1(k7_relat_1(sK3,X10))) )),
% 1.49/0.55    inference(resolution,[],[f63,f53])).
% 1.49/0.55  fof(f53,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f33])).
% 1.49/0.55  fof(f33,plain,(
% 1.49/0.55    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f5])).
% 1.49/0.55  fof(f5,axiom,(
% 1.49/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.49/0.55  fof(f63,plain,(
% 1.49/0.55    v1_relat_1(sK3)),
% 1.49/0.55    inference(subsumption_resolution,[],[f60,f46])).
% 1.49/0.55  fof(f46,plain,(
% 1.49/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f6])).
% 1.49/0.55  fof(f6,axiom,(
% 1.49/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.49/0.55  fof(f60,plain,(
% 1.49/0.55    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | v1_relat_1(sK3)),
% 1.49/0.55    inference(resolution,[],[f37,f45])).
% 1.49/0.55  fof(f45,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f23])).
% 1.49/0.55  fof(f23,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f3])).
% 1.49/0.55  fof(f3,axiom,(
% 1.49/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.49/0.55  fof(f239,plain,(
% 1.49/0.55    ( ! [X14] : (k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X14))) = k7_relat_1(k7_relat_1(sK3,X14),k1_relat_1(k7_relat_1(sK3,X14)))) )),
% 1.49/0.55    inference(resolution,[],[f66,f71])).
% 1.49/0.55  fof(f71,plain,(
% 1.49/0.55    ( ! [X9] : (r1_tarski(k1_relat_1(k7_relat_1(sK3,X9)),X9)) )),
% 1.49/0.55    inference(resolution,[],[f63,f52])).
% 1.49/0.55  fof(f52,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f32])).
% 1.49/0.55  fof(f32,plain,(
% 1.49/0.55    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f10])).
% 1.49/0.55  fof(f10,axiom,(
% 1.49/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 1.49/0.55  fof(f66,plain,(
% 1.49/0.55    ( ! [X4,X3] : (~r1_tarski(X3,X4) | k7_relat_1(k7_relat_1(sK3,X4),X3) = k7_relat_1(sK3,X3)) )),
% 1.49/0.55    inference(resolution,[],[f63,f47])).
% 1.49/0.55  fof(f47,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f25])).
% 1.49/0.55  fof(f25,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.49/0.55    inference(flattening,[],[f24])).
% 1.49/0.55  fof(f24,plain,(
% 1.49/0.55    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.49/0.55    inference(ennf_transformation,[],[f7])).
% 1.49/0.55  fof(f7,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).
% 1.49/0.55  fof(f219,plain,(
% 1.49/0.55    ( ! [X15] : (r1_tarski(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X15))),sK3)) )),
% 1.49/0.55    inference(forward_demodulation,[],[f216,f68])).
% 1.49/0.55  fof(f68,plain,(
% 1.49/0.55    sK3 = k7_relat_1(sK3,k1_relat_1(sK3))),
% 1.49/0.55    inference(resolution,[],[f63,f49])).
% 1.49/0.55  fof(f216,plain,(
% 1.49/0.55    ( ! [X15] : (r1_tarski(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X15))),k7_relat_1(sK3,k1_relat_1(sK3)))) )),
% 1.49/0.55    inference(resolution,[],[f69,f70])).
% 1.49/0.55  fof(f70,plain,(
% 1.49/0.55    ( ! [X8] : (r1_tarski(k1_relat_1(k7_relat_1(sK3,X8)),k1_relat_1(sK3))) )),
% 1.49/0.55    inference(resolution,[],[f63,f51])).
% 1.49/0.55  fof(f51,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f31])).
% 1.49/0.55  fof(f31,plain,(
% 1.49/0.55    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f11])).
% 1.49/0.55  fof(f11,axiom,(
% 1.49/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).
% 1.49/0.55  fof(f69,plain,(
% 1.49/0.55    ( ! [X6,X7] : (~r1_tarski(X6,X7) | r1_tarski(k7_relat_1(sK3,X6),k7_relat_1(sK3,X7))) )),
% 1.49/0.55    inference(resolution,[],[f63,f50])).
% 1.49/0.55  fof(f50,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f30])).
% 1.49/0.55  fof(f30,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.49/0.55    inference(flattening,[],[f29])).
% 1.49/0.55  fof(f29,plain,(
% 1.49/0.55    ! [X0,X1,X2] : ((r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.49/0.55    inference(ennf_transformation,[],[f8])).
% 1.49/0.55  fof(f8,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).
% 1.49/0.55  fof(f390,plain,(
% 1.49/0.55    ( ! [X1] : (~r1_tarski(k7_relat_1(sK3,sK1),k2_zfmisc_1(X1,sK2))) )),
% 1.49/0.55    inference(resolution,[],[f140,f43])).
% 1.49/0.55  fof(f43,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f2])).
% 1.49/0.55  fof(f140,plain,(
% 1.49/0.55    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 1.49/0.55    inference(resolution,[],[f95,f41])).
% 1.49/0.55  fof(f41,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f20])).
% 1.49/0.55  fof(f20,plain,(
% 1.49/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.55    inference(ennf_transformation,[],[f13])).
% 1.49/0.55  fof(f13,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.49/0.55  fof(f95,plain,(
% 1.49/0.55    ~v5_relat_1(k7_relat_1(sK3,sK1),sK2)),
% 1.49/0.55    inference(subsumption_resolution,[],[f91,f72])).
% 1.49/0.55  fof(f91,plain,(
% 1.49/0.55    ~v1_relat_1(k7_relat_1(sK3,sK1)) | ~v5_relat_1(k7_relat_1(sK3,sK1),sK2)),
% 1.49/0.55    inference(resolution,[],[f79,f55])).
% 1.49/0.55  fof(f55,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f34])).
% 1.49/0.55  fof(f34,plain,(
% 1.49/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f4])).
% 1.49/0.55  fof(f4,axiom,(
% 1.49/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.49/0.55  fof(f79,plain,(
% 1.49/0.55    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)),
% 1.49/0.55    inference(subsumption_resolution,[],[f78,f71])).
% 1.49/0.55  fof(f78,plain,(
% 1.49/0.55    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)),
% 1.49/0.55    inference(subsumption_resolution,[],[f75,f72])).
% 1.49/0.55  fof(f75,plain,(
% 1.49/0.55    ~v1_relat_1(k7_relat_1(sK3,sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)),
% 1.49/0.55    inference(resolution,[],[f62,f42])).
% 1.49/0.55  fof(f42,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f22])).
% 1.49/0.55  fof(f22,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.49/0.55    inference(flattening,[],[f21])).
% 1.49/0.55  fof(f21,plain,(
% 1.49/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.49/0.55    inference(ennf_transformation,[],[f15])).
% 1.49/0.55  fof(f15,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.49/0.55  fof(f62,plain,(
% 1.49/0.55    ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.49/0.55    inference(backward_demodulation,[],[f38,f59])).
% 1.49/0.55  fof(f59,plain,(
% 1.49/0.55    ( ! [X0] : (k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 1.49/0.55    inference(resolution,[],[f37,f39])).
% 1.49/0.55  fof(f39,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f19])).
% 1.49/0.55  fof(f19,plain,(
% 1.49/0.55    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.55    inference(ennf_transformation,[],[f14])).
% 1.49/0.55  fof(f14,axiom,(
% 1.49/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 1.49/0.55  fof(f38,plain,(
% 1.49/0.55    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.49/0.55    inference(cnf_transformation,[],[f18])).
% 1.49/0.55  % SZS output end Proof for theBenchmark
% 1.49/0.55  % (18439)------------------------------
% 1.49/0.55  % (18439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (18439)Termination reason: Refutation
% 1.49/0.55  
% 1.49/0.55  % (18439)Memory used [KB]: 2686
% 1.49/0.55  % (18439)Time elapsed: 0.137 s
% 1.49/0.55  % (18439)------------------------------
% 1.49/0.55  % (18439)------------------------------
% 1.49/0.56  % (18417)Success in time 0.195 s
%------------------------------------------------------------------------------

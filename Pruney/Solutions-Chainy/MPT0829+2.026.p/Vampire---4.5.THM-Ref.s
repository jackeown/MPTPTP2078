%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 128 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  143 ( 402 expanded)
%              Number of equality atoms :   34 ( 102 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f154,plain,(
    $false ),
    inference(global_subsumption,[],[f30,f96,f147])).

fof(f147,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f88,f144])).

fof(f144,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f141,f33])).

fof(f33,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f141,plain,(
    k2_relat_1(sK2) = k2_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[],[f33,f118])).

fof(f118,plain,(
    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f92,f114])).

fof(f114,plain,(
    k6_relat_1(sK1) = k5_relat_1(k6_relat_1(k2_relat_1(sK2)),k6_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f112,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(global_subsumption,[],[f31,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f36,f32])).

fof(f32,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f112,plain,(
    r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f110,f88])).

fof(f110,plain,(
    r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f29,f28,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k6_relat_1(X2),X3)
      | r1_tarski(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
    & r1_tarski(k6_relat_1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
        & r1_tarski(k6_relat_1(X1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
        | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
      & r1_tarski(k6_relat_1(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).

fof(f29,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f92,plain,(
    k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k6_relat_1(k2_relat_1(sK2)),k6_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f69,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(global_subsumption,[],[f31,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f37,f33])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f69,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f54,f67,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f67,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f28,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f54,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f35,f28,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f88,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f28,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f96,plain,(
    r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f29,f28,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k6_relat_1(X2),X3)
      | r1_tarski(X2,k1_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f30,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (7065)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.47  % (7065)Refutation not found, incomplete strategy% (7065)------------------------------
% 0.20/0.47  % (7065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (7057)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.47  % (7065)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (7065)Memory used [KB]: 10618
% 0.20/0.47  % (7065)Time elapsed: 0.053 s
% 0.20/0.47  % (7065)------------------------------
% 0.20/0.47  % (7065)------------------------------
% 0.20/0.48  % (7059)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.48  % (7060)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (7069)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.49  % (7056)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (7077)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (7068)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.50  % (7076)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (7062)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (7055)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (7062)Refutation not found, incomplete strategy% (7062)------------------------------
% 0.20/0.50  % (7062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7062)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7062)Memory used [KB]: 6140
% 0.20/0.50  % (7062)Time elapsed: 0.093 s
% 0.20/0.50  % (7062)------------------------------
% 0.20/0.50  % (7062)------------------------------
% 0.20/0.51  % (7066)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.51  % (7069)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(global_subsumption,[],[f30,f96,f147])).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.51    inference(backward_demodulation,[],[f88,f144])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    sK1 = k2_relat_1(sK2)),
% 0.20/0.51    inference(forward_demodulation,[],[f141,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    k2_relat_1(sK2) = k2_relat_1(k6_relat_1(sK1))),
% 0.20/0.51    inference(superposition,[],[f33,f118])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))),
% 0.20/0.51    inference(backward_demodulation,[],[f92,f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    k6_relat_1(sK1) = k5_relat_1(k6_relat_1(k2_relat_1(sK2)),k6_relat_1(sK1))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f112,f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 0.20/0.51    inference(global_subsumption,[],[f31,f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.51    inference(superposition,[],[f36,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    r1_tarski(sK1,k2_relat_1(sK2))),
% 0.20/0.51    inference(forward_demodulation,[],[f110,f88])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f29,f28,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r1_tarski(k6_relat_1(X2),X3) | r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(flattening,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    (sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(flattening,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f11])).
% 0.20/0.51  fof(f11,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    r1_tarski(k6_relat_1(sK1),sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k6_relat_1(k2_relat_1(sK2)),k6_relat_1(sK1))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f69,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 0.20/0.51    inference(global_subsumption,[],[f31,f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.51    inference(superposition,[],[f37,f33])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f54,f67,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    v5_relat_1(sK2,sK1)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f28,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    v1_relat_1(sK2)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f35,f28,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f28,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f29,f28,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r1_tarski(k6_relat_1(X2),X3) | r1_tarski(X2,k1_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (7069)------------------------------
% 0.20/0.51  % (7069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7069)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (7069)Memory used [KB]: 10746
% 0.20/0.51  % (7069)Time elapsed: 0.067 s
% 0.20/0.51  % (7069)------------------------------
% 0.20/0.51  % (7069)------------------------------
% 0.20/0.51  % (7054)Success in time 0.154 s
%------------------------------------------------------------------------------

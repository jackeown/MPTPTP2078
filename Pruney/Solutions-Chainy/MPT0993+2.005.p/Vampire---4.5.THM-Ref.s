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
% DateTime   : Thu Dec  3 13:03:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 (  88 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :   14
%              Number of atoms          :  135 ( 273 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(subsumption_resolution,[],[f70,f48])).

fof(f48,plain,(
    r2_relset_1(sK0,sK1,sK3,sK3) ),
    inference(resolution,[],[f25,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

fof(f70,plain,(
    ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    inference(backward_demodulation,[],[f51,f69])).

fof(f69,plain,(
    sK3 = k7_relat_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f68,f45])).

fof(f45,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f25,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f68,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k7_relat_1(sK3,sK2) ),
    inference(resolution,[],[f63,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f63,plain,(
    v4_relat_1(sK3,sK2) ),
    inference(resolution,[],[f59,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(resolution,[],[f58,f26])).

fof(f26,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) ) ),
    inference(resolution,[],[f56,f42])).

fof(f42,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP4(X4,X3,X0)
      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(general_splitting,[],[f31,f41_D])).

fof(f41,plain,(
    ! [X4,X2,X0,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ r1_tarski(X2,X3)
      | sP4(X4,X3,X0) ) ),
    inference(cnf_transformation,[],[f41_D])).

fof(f41_D,plain,(
    ! [X0,X3,X4] :
      ( ! [X2] :
          ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ r1_tarski(X2,X3) )
    <=> ~ sP4(X4,X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).

fof(f56,plain,(
    sP4(sK3,sK1,sK0) ),
    inference(resolution,[],[f49,f40])).

fof(f40,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
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

fof(f49,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK1,X1)
      | sP4(sK3,X1,sK0) ) ),
    inference(resolution,[],[f25,f41])).

fof(f51,plain,(
    ~ r2_relset_1(sK0,sK1,k7_relat_1(sK3,sK2),sK3) ),
    inference(backward_demodulation,[],[f27,f50])).

fof(f50,plain,(
    ! [X0] : k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(subsumption_resolution,[],[f47,f24])).

fof(f24,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f25,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f27,plain,(
    ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.48  % (27055)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.48  % (27052)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.49  % (27060)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.49  % (27055)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f70,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.22/0.49    inference(resolution,[],[f25,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.22/0.49    inference(equality_resolution,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(flattening,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.22/0.49    inference(backward_demodulation,[],[f51,f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    sK3 = k7_relat_1(sK3,sK2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f68,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    v1_relat_1(sK3)),
% 0.22/0.49    inference(resolution,[],[f25,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ~v1_relat_1(sK3) | sK3 = k7_relat_1(sK3,sK2)),
% 0.22/0.49    inference(resolution,[],[f63,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    v4_relat_1(sK3,sK2)),
% 0.22/0.49    inference(resolution,[],[f59,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.49    inference(resolution,[],[f58,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    r1_tarski(sK0,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(sK0,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) )),
% 0.22/0.49    inference(resolution,[],[f56,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X4,X0,X3,X1] : (~sP4(X4,X3,X0) | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(general_splitting,[],[f31,f41_D])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~r1_tarski(X2,X3) | sP4(X4,X3,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f41_D])).
% 0.22/0.49  fof(f41_D,plain,(
% 0.22/0.49    ( ! [X0,X3,X4] : (( ! [X2] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~r1_tarski(X2,X3)) ) <=> ~sP4(X4,X3,X0)) )),
% 0.22/0.49    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    sP4(sK3,sK1,sK0)),
% 0.22/0.49    inference(resolution,[],[f49,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.49    inference(equality_resolution,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X1] : (~r1_tarski(sK1,X1) | sP4(sK3,X1,sK0)) )),
% 0.22/0.49    inference(resolution,[],[f25,f41])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK1,k7_relat_1(sK3,sK2),sK3)),
% 0.22/0.49    inference(backward_demodulation,[],[f27,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f47,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    v1_funct_1(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_1(sK3) | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.22/0.49    inference(resolution,[],[f25,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.49    inference(flattening,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (27055)------------------------------
% 0.22/0.49  % (27055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (27055)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (27055)Memory used [KB]: 6140
% 0.22/0.49  % (27055)Time elapsed: 0.074 s
% 0.22/0.49  % (27055)------------------------------
% 0.22/0.49  % (27055)------------------------------
% 0.22/0.49  % (27048)Success in time 0.135 s
%------------------------------------------------------------------------------

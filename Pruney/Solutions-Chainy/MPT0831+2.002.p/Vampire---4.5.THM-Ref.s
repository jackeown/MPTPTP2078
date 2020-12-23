%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:52 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 (  74 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :   13
%              Number of atoms          :  116 ( 182 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(subsumption_resolution,[],[f66,f46])).

fof(f46,plain,(
    r2_relset_1(sK1,sK0,sK3,sK3) ),
    inference(resolution,[],[f23,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

fof(f66,plain,(
    ~ r2_relset_1(sK1,sK0,sK3,sK3) ),
    inference(backward_demodulation,[],[f48,f65])).

fof(f65,plain,(
    sK3 = k7_relat_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f64,f43])).

fof(f43,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f23,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f64,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k7_relat_1(sK3,sK2) ),
    inference(resolution,[],[f60,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f60,plain,(
    v4_relat_1(sK3,sK2) ),
    inference(resolution,[],[f56,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(resolution,[],[f55,f24])).

fof(f24,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ) ),
    inference(resolution,[],[f53,f40])).

fof(f40,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP4(X4,X3,X0)
      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(general_splitting,[],[f29,f39_D])).

fof(f39,plain,(
    ! [X4,X2,X0,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ r1_tarski(X2,X3)
      | sP4(X4,X3,X0) ) ),
    inference(cnf_transformation,[],[f39_D])).

fof(f39_D,plain,(
    ! [X0,X3,X4] :
      ( ! [X2] :
          ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ r1_tarski(X2,X3) )
    <=> ~ sP4(X4,X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

fof(f53,plain,(
    sP4(sK3,sK0,sK1) ),
    inference(resolution,[],[f47,f38])).

fof(f38,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f47,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK0,X1)
      | sP4(sK3,X1,sK1) ) ),
    inference(resolution,[],[f23,f39])).

fof(f48,plain,(
    ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) ),
    inference(backward_demodulation,[],[f25,f45])).

fof(f45,plain,(
    ! [X0] : k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(resolution,[],[f23,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f25,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:34:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.43  % (10328)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.43  % (10328)Refutation found. Thanks to Tanya!
% 0.19/0.43  % SZS status Theorem for theBenchmark
% 0.19/0.43  % SZS output start Proof for theBenchmark
% 0.19/0.43  fof(f67,plain,(
% 0.19/0.43    $false),
% 0.19/0.43    inference(subsumption_resolution,[],[f66,f46])).
% 0.19/0.43  fof(f46,plain,(
% 0.19/0.43    r2_relset_1(sK1,sK0,sK3,sK3)),
% 0.19/0.43    inference(resolution,[],[f23,f41])).
% 0.19/0.43  fof(f41,plain,(
% 0.19/0.43    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.19/0.43    inference(duplicate_literal_removal,[],[f36])).
% 0.19/0.43  fof(f36,plain,(
% 0.19/0.43    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.19/0.43    inference(equality_resolution,[],[f26])).
% 0.19/0.43  fof(f26,plain,(
% 0.19/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f15])).
% 0.19/0.43  fof(f15,plain,(
% 0.19/0.43    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.43    inference(flattening,[],[f14])).
% 0.19/0.43  fof(f14,plain,(
% 0.19/0.43    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.43    inference(ennf_transformation,[],[f7])).
% 0.19/0.43  fof(f7,axiom,(
% 0.19/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.19/0.43  fof(f23,plain,(
% 0.19/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.43    inference(cnf_transformation,[],[f13])).
% 0.19/0.43  fof(f13,plain,(
% 0.19/0.43    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.19/0.43    inference(flattening,[],[f12])).
% 0.19/0.43  fof(f12,plain,(
% 0.19/0.43    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.19/0.43    inference(ennf_transformation,[],[f10])).
% 0.19/0.43  fof(f10,negated_conjecture,(
% 0.19/0.43    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.19/0.43    inference(negated_conjecture,[],[f9])).
% 0.19/0.43  fof(f9,conjecture,(
% 0.19/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).
% 0.19/0.43  fof(f66,plain,(
% 0.19/0.43    ~r2_relset_1(sK1,sK0,sK3,sK3)),
% 0.19/0.43    inference(backward_demodulation,[],[f48,f65])).
% 0.19/0.43  fof(f65,plain,(
% 0.19/0.43    sK3 = k7_relat_1(sK3,sK2)),
% 0.19/0.43    inference(subsumption_resolution,[],[f64,f43])).
% 0.19/0.43  fof(f43,plain,(
% 0.19/0.43    v1_relat_1(sK3)),
% 0.19/0.43    inference(resolution,[],[f23,f35])).
% 0.19/0.43  fof(f35,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f22])).
% 0.19/0.43  fof(f22,plain,(
% 0.19/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.43    inference(ennf_transformation,[],[f4])).
% 0.19/0.43  fof(f4,axiom,(
% 0.19/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.43  fof(f64,plain,(
% 0.19/0.43    ~v1_relat_1(sK3) | sK3 = k7_relat_1(sK3,sK2)),
% 0.19/0.43    inference(resolution,[],[f60,f33])).
% 0.19/0.43  fof(f33,plain,(
% 0.19/0.43    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.19/0.43    inference(cnf_transformation,[],[f20])).
% 0.19/0.43  fof(f20,plain,(
% 0.19/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.43    inference(flattening,[],[f19])).
% 0.19/0.43  fof(f19,plain,(
% 0.19/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.43    inference(ennf_transformation,[],[f3])).
% 0.19/0.43  fof(f3,axiom,(
% 0.19/0.43    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.19/0.43  fof(f60,plain,(
% 0.19/0.43    v4_relat_1(sK3,sK2)),
% 0.19/0.43    inference(resolution,[],[f56,f34])).
% 0.19/0.43  fof(f34,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f21])).
% 0.19/0.43  fof(f21,plain,(
% 0.19/0.43    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.43    inference(ennf_transformation,[],[f11])).
% 0.19/0.43  fof(f11,plain,(
% 0.19/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.19/0.43    inference(pure_predicate_removal,[],[f5])).
% 0.19/0.43  fof(f5,axiom,(
% 0.19/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.43  fof(f56,plain,(
% 0.19/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.19/0.43    inference(resolution,[],[f55,f24])).
% 0.19/0.43  fof(f24,plain,(
% 0.19/0.43    r1_tarski(sK1,sK2)),
% 0.19/0.43    inference(cnf_transformation,[],[f13])).
% 0.19/0.43  fof(f55,plain,(
% 0.19/0.43    ( ! [X0] : (~r1_tarski(sK1,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) )),
% 0.19/0.43    inference(resolution,[],[f53,f40])).
% 0.19/0.43  fof(f40,plain,(
% 0.19/0.43    ( ! [X4,X0,X3,X1] : (~sP4(X4,X3,X0) | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~r1_tarski(X0,X1)) )),
% 0.19/0.43    inference(general_splitting,[],[f29,f39_D])).
% 0.19/0.43  fof(f39,plain,(
% 0.19/0.43    ( ! [X4,X2,X0,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~r1_tarski(X2,X3) | sP4(X4,X3,X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f39_D])).
% 0.19/0.43  fof(f39_D,plain,(
% 0.19/0.43    ( ! [X0,X3,X4] : (( ! [X2] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~r1_tarski(X2,X3)) ) <=> ~sP4(X4,X3,X0)) )),
% 0.19/0.43    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 0.19/0.43  fof(f29,plain,(
% 0.19/0.43    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f18])).
% 0.19/0.43  fof(f18,plain,(
% 0.19/0.43    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.19/0.43    inference(flattening,[],[f17])).
% 0.19/0.43  fof(f17,plain,(
% 0.19/0.43    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.19/0.43    inference(ennf_transformation,[],[f8])).
% 0.19/0.43  fof(f8,axiom,(
% 0.19/0.43    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).
% 0.19/0.43  fof(f53,plain,(
% 0.19/0.43    sP4(sK3,sK0,sK1)),
% 0.19/0.43    inference(resolution,[],[f47,f38])).
% 0.19/0.43  fof(f38,plain,(
% 0.19/0.43    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.43    inference(equality_resolution,[],[f30])).
% 0.19/0.43  fof(f30,plain,(
% 0.19/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.19/0.43    inference(cnf_transformation,[],[f1])).
% 0.19/0.43  fof(f1,axiom,(
% 0.19/0.43    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.43  fof(f47,plain,(
% 0.19/0.43    ( ! [X1] : (~r1_tarski(sK0,X1) | sP4(sK3,X1,sK1)) )),
% 0.19/0.43    inference(resolution,[],[f23,f39])).
% 0.19/0.43  fof(f48,plain,(
% 0.19/0.43    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)),
% 0.19/0.43    inference(backward_demodulation,[],[f25,f45])).
% 0.19/0.43  fof(f45,plain,(
% 0.19/0.43    ( ! [X0] : (k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.19/0.43    inference(resolution,[],[f23,f28])).
% 0.19/0.43  fof(f28,plain,(
% 0.19/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f16])).
% 0.19/0.43  fof(f16,plain,(
% 0.19/0.43    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.43    inference(ennf_transformation,[],[f6])).
% 0.19/0.43  fof(f6,axiom,(
% 0.19/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.19/0.43  fof(f25,plain,(
% 0.19/0.43    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.19/0.43    inference(cnf_transformation,[],[f13])).
% 0.19/0.43  % SZS output end Proof for theBenchmark
% 0.19/0.43  % (10328)------------------------------
% 0.19/0.43  % (10328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (10328)Termination reason: Refutation
% 0.19/0.43  
% 0.19/0.43  % (10328)Memory used [KB]: 6140
% 0.19/0.43  % (10328)Time elapsed: 0.055 s
% 0.19/0.43  % (10328)------------------------------
% 0.19/0.43  % (10328)------------------------------
% 0.19/0.44  % (10322)Success in time 0.09 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:56:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 158 expanded)
%              Number of leaves         :   12 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  124 ( 343 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f269,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f78,f137,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f137,plain,(
    ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ),
    inference(unit_resulting_resolution,[],[f135,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f135,plain,(
    ~ v5_relat_1(k7_relat_1(sK3,sK1),sK2) ),
    inference(subsumption_resolution,[],[f132,f111])).

fof(f111,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f45,f79,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f56,f34])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK3,X0),sK3) ),
    inference(unit_resulting_resolution,[],[f45,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f45,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f37,f29,f35])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

% (26705)Refutation not found, incomplete strategy% (26705)------------------------------
% (26705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26705)Termination reason: Refutation not found, incomplete strategy

% (26705)Memory used [KB]: 10618
% (26705)Time elapsed: 0.075 s
% (26705)------------------------------
% (26705)------------------------------
fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f132,plain,
    ( ~ v5_relat_1(k7_relat_1(sK3,sK1),sK2)
    | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f127,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f127,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) ),
    inference(subsumption_resolution,[],[f126,f111])).

fof(f126,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f84,f57])).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f45,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f84,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f77,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f77,plain,(
    ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(backward_demodulation,[],[f30,f44])).

fof(f44,plain,(
    ! [X0] : k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f29,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f30,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f56,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f46,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f29,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:29:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.43  % (26704)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.46  % (26703)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.46  % (26716)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.46  % (26711)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.47  % (26701)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.48  % (26705)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.48  % (26702)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.48  % (26716)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f269,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f78,f137,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.48    inference(nnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f135,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.48    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    ~v5_relat_1(k7_relat_1(sK3,sK1),sK2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f132,f111])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f45,f79,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(sK3))) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f56,f34])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),sK3)) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f45,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    v1_relat_1(sK3)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f37,f29,f35])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.48    inference(negated_conjecture,[],[f11])).
% 0.20/0.48  fof(f11,conjecture,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).
% 0.20/0.48  % (26705)Refutation not found, incomplete strategy% (26705)------------------------------
% 0.20/0.48  % (26705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (26705)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (26705)Memory used [KB]: 10618
% 0.20/0.48  % (26705)Time elapsed: 0.075 s
% 0.20/0.48  % (26705)------------------------------
% 0.20/0.48  % (26705)------------------------------
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    ~v5_relat_1(k7_relat_1(sK3,sK1),sK2) | ~v1_relat_1(k7_relat_1(sK3,sK1))),
% 0.20/0.48    inference(resolution,[],[f127,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f126,f111])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) | ~v1_relat_1(k7_relat_1(sK3,sK1))),
% 0.20/0.48    inference(subsumption_resolution,[],[f84,f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f45,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | ~v1_relat_1(k7_relat_1(sK3,sK1))),
% 0.20/0.48    inference(resolution,[],[f77,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.48    inference(backward_demodulation,[],[f30,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0] : (k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f29,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK2))) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f46,f56,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f29,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (26716)------------------------------
% 0.20/0.48  % (26716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (26716)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (26716)Memory used [KB]: 1663
% 0.20/0.48  % (26716)Time elapsed: 0.073 s
% 0.20/0.48  % (26716)------------------------------
% 0.20/0.48  % (26716)------------------------------
% 0.20/0.48  % (26698)Success in time 0.135 s
%------------------------------------------------------------------------------

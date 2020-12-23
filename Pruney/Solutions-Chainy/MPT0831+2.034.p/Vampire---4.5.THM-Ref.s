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
% DateTime   : Thu Dec  3 12:56:56 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 106 expanded)
%              Number of leaves         :   10 (  25 expanded)
%              Depth                    :   14
%              Number of atoms          :  151 ( 306 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(subsumption_resolution,[],[f61,f28])).

fof(f28,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f23])).

% (21481)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f61,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f60,f47])).

fof(f47,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f35,f27])).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f60,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK3,X0)
      | ~ r1_tarski(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f59,f44])).

fof(f44,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f43,f31])).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f43,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f30,f27])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f59,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | ~ v1_relat_1(sK3)
      | ~ v4_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f58,f55])).

fof(f55,plain,(
    ~ v4_relat_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f54,f44])).

fof(f54,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f53,f50])).

fof(f50,plain,(
    r2_relset_1(sK1,sK0,sK3,sK3) ),
    inference(resolution,[],[f42,f27])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f53,plain,
    ( ~ r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f52,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f52,plain,(
    ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) ),
    inference(subsumption_resolution,[],[f51,f27])).

fof(f51,plain,
    ( ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f29,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f29,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f49,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(X0,X1)
      | v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f37,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (1214349313)
% 0.13/0.37  ipcrm: permission denied for id (1214513158)
% 0.13/0.38  ipcrm: permission denied for id (1214709773)
% 0.13/0.38  ipcrm: permission denied for id (1214742542)
% 0.13/0.39  ipcrm: permission denied for id (1214939158)
% 0.13/0.40  ipcrm: permission denied for id (1215070234)
% 0.21/0.40  ipcrm: permission denied for id (1215103004)
% 0.21/0.41  ipcrm: permission denied for id (1215234080)
% 0.21/0.41  ipcrm: permission denied for id (1215365158)
% 0.21/0.42  ipcrm: permission denied for id (1215463467)
% 0.21/0.42  ipcrm: permission denied for id (1215561774)
% 0.21/0.43  ipcrm: permission denied for id (1215692850)
% 0.21/0.43  ipcrm: permission denied for id (1215725619)
% 0.21/0.44  ipcrm: permission denied for id (1215823927)
% 0.21/0.44  ipcrm: permission denied for id (1215856696)
% 0.21/0.44  ipcrm: permission denied for id (1215955003)
% 0.21/0.44  ipcrm: permission denied for id (1215987772)
% 0.21/0.45  ipcrm: permission denied for id (1216020542)
% 0.21/0.45  ipcrm: permission denied for id (1216118849)
% 0.21/0.45  ipcrm: permission denied for id (1216151618)
% 0.21/0.45  ipcrm: permission denied for id (1216184387)
% 0.21/0.45  ipcrm: permission denied for id (1216249925)
% 0.21/0.46  ipcrm: permission denied for id (1216282694)
% 0.21/0.46  ipcrm: permission denied for id (1216315463)
% 0.21/0.46  ipcrm: permission denied for id (1216413772)
% 0.21/0.46  ipcrm: permission denied for id (1216446541)
% 0.21/0.47  ipcrm: permission denied for id (1216577617)
% 0.21/0.47  ipcrm: permission denied for id (1216643155)
% 0.21/0.48  ipcrm: permission denied for id (1216872539)
% 0.21/0.49  ipcrm: permission denied for id (1216970847)
% 0.21/0.49  ipcrm: permission denied for id (1217003616)
% 0.21/0.49  ipcrm: permission denied for id (1217101924)
% 0.21/0.50  ipcrm: permission denied for id (1217298539)
% 0.21/0.50  ipcrm: permission denied for id (1217331308)
% 0.21/0.50  ipcrm: permission denied for id (1217364077)
% 0.21/0.51  ipcrm: permission denied for id (1217396846)
% 0.21/0.51  ipcrm: permission denied for id (1217495154)
% 0.21/0.52  ipcrm: permission denied for id (1217626231)
% 0.21/0.52  ipcrm: permission denied for id (1217691769)
% 0.21/0.52  ipcrm: permission denied for id (1217724538)
% 0.21/0.52  ipcrm: permission denied for id (1217790076)
% 0.21/0.53  ipcrm: permission denied for id (1217822845)
% 0.92/0.65  % (21468)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.92/0.66  % (21469)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.92/0.66  % (21470)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.92/0.67  % (21469)Refutation found. Thanks to Tanya!
% 0.92/0.67  % SZS status Theorem for theBenchmark
% 0.92/0.67  % (21467)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.92/0.67  % SZS output start Proof for theBenchmark
% 0.92/0.67  fof(f63,plain,(
% 0.92/0.67    $false),
% 0.92/0.67    inference(subsumption_resolution,[],[f61,f28])).
% 0.92/0.67  fof(f28,plain,(
% 0.92/0.67    r1_tarski(sK1,sK2)),
% 0.92/0.67    inference(cnf_transformation,[],[f24])).
% 0.92/0.67  fof(f24,plain,(
% 0.92/0.67    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.92/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f23])).
% 0.92/0.67  % (21481)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.92/0.67  fof(f23,plain,(
% 0.92/0.67    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.92/0.67    introduced(choice_axiom,[])).
% 0.92/0.67  fof(f12,plain,(
% 0.92/0.67    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.92/0.67    inference(flattening,[],[f11])).
% 0.92/0.67  fof(f11,plain,(
% 0.92/0.67    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.92/0.67    inference(ennf_transformation,[],[f10])).
% 0.92/0.67  fof(f10,negated_conjecture,(
% 0.92/0.67    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.92/0.67    inference(negated_conjecture,[],[f9])).
% 0.92/0.67  fof(f9,conjecture,(
% 0.92/0.67    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.92/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).
% 0.92/0.67  fof(f61,plain,(
% 0.92/0.67    ~r1_tarski(sK1,sK2)),
% 0.92/0.67    inference(resolution,[],[f60,f47])).
% 0.92/0.67  fof(f47,plain,(
% 0.92/0.67    v4_relat_1(sK3,sK1)),
% 0.92/0.67    inference(resolution,[],[f35,f27])).
% 0.92/0.67  fof(f27,plain,(
% 0.92/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.92/0.67    inference(cnf_transformation,[],[f24])).
% 0.92/0.67  fof(f35,plain,(
% 0.92/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.92/0.67    inference(cnf_transformation,[],[f17])).
% 0.92/0.67  fof(f17,plain,(
% 0.92/0.67    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.92/0.67    inference(ennf_transformation,[],[f6])).
% 0.92/0.67  fof(f6,axiom,(
% 0.92/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.92/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.92/0.67  fof(f60,plain,(
% 0.92/0.67    ( ! [X0] : (~v4_relat_1(sK3,X0) | ~r1_tarski(X0,sK2)) )),
% 0.92/0.67    inference(subsumption_resolution,[],[f59,f44])).
% 0.92/0.67  fof(f44,plain,(
% 0.92/0.67    v1_relat_1(sK3)),
% 0.92/0.67    inference(subsumption_resolution,[],[f43,f31])).
% 0.92/0.67  fof(f31,plain,(
% 0.92/0.67    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.92/0.67    inference(cnf_transformation,[],[f4])).
% 0.92/0.67  fof(f4,axiom,(
% 0.92/0.67    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.92/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.92/0.67  fof(f43,plain,(
% 0.92/0.67    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 0.92/0.67    inference(resolution,[],[f30,f27])).
% 0.92/0.67  fof(f30,plain,(
% 0.92/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.92/0.67    inference(cnf_transformation,[],[f13])).
% 0.92/0.67  fof(f13,plain,(
% 0.92/0.67    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.92/0.67    inference(ennf_transformation,[],[f2])).
% 0.92/0.67  fof(f2,axiom,(
% 0.92/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.92/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.92/0.67  fof(f59,plain,(
% 0.92/0.67    ( ! [X0] : (~r1_tarski(X0,sK2) | ~v1_relat_1(sK3) | ~v4_relat_1(sK3,X0)) )),
% 0.92/0.67    inference(resolution,[],[f58,f55])).
% 0.92/0.67  fof(f55,plain,(
% 0.92/0.67    ~v4_relat_1(sK3,sK2)),
% 0.92/0.67    inference(subsumption_resolution,[],[f54,f44])).
% 0.92/0.67  fof(f54,plain,(
% 0.92/0.67    ~v4_relat_1(sK3,sK2) | ~v1_relat_1(sK3)),
% 0.92/0.67    inference(subsumption_resolution,[],[f53,f50])).
% 0.92/0.67  fof(f50,plain,(
% 0.92/0.67    r2_relset_1(sK1,sK0,sK3,sK3)),
% 0.92/0.67    inference(resolution,[],[f42,f27])).
% 0.92/0.67  fof(f42,plain,(
% 0.92/0.67    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.92/0.67    inference(duplicate_literal_removal,[],[f41])).
% 0.92/0.67  fof(f41,plain,(
% 0.92/0.67    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.92/0.67    inference(equality_resolution,[],[f40])).
% 0.92/0.67  fof(f40,plain,(
% 0.92/0.67    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.92/0.67    inference(cnf_transformation,[],[f26])).
% 0.92/0.67  fof(f26,plain,(
% 0.92/0.67    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.92/0.67    inference(nnf_transformation,[],[f22])).
% 0.92/0.67  fof(f22,plain,(
% 0.92/0.67    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.92/0.67    inference(flattening,[],[f21])).
% 0.92/0.67  fof(f21,plain,(
% 0.92/0.67    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.92/0.67    inference(ennf_transformation,[],[f8])).
% 0.92/0.67  fof(f8,axiom,(
% 0.92/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.92/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.92/0.67  fof(f53,plain,(
% 0.92/0.67    ~r2_relset_1(sK1,sK0,sK3,sK3) | ~v4_relat_1(sK3,sK2) | ~v1_relat_1(sK3)),
% 0.92/0.67    inference(superposition,[],[f52,f34])).
% 0.92/0.67  fof(f34,plain,(
% 0.92/0.67    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.92/0.67    inference(cnf_transformation,[],[f16])).
% 0.92/0.67  fof(f16,plain,(
% 0.92/0.67    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.92/0.67    inference(flattening,[],[f15])).
% 0.92/0.67  fof(f15,plain,(
% 0.92/0.67    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.92/0.67    inference(ennf_transformation,[],[f5])).
% 0.92/0.67  fof(f5,axiom,(
% 0.92/0.67    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.92/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.92/0.67  fof(f52,plain,(
% 0.92/0.67    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)),
% 0.92/0.67    inference(subsumption_resolution,[],[f51,f27])).
% 0.92/0.67  fof(f51,plain,(
% 0.92/0.67    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.92/0.67    inference(superposition,[],[f29,f38])).
% 0.92/0.67  fof(f38,plain,(
% 0.92/0.67    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.92/0.67    inference(cnf_transformation,[],[f20])).
% 0.92/0.67  fof(f20,plain,(
% 0.92/0.67    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.92/0.67    inference(ennf_transformation,[],[f7])).
% 0.92/0.67  fof(f7,axiom,(
% 0.92/0.67    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.92/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.92/0.67  fof(f29,plain,(
% 0.92/0.67    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.92/0.67    inference(cnf_transformation,[],[f24])).
% 0.92/0.67  fof(f58,plain,(
% 0.92/0.67    ( ! [X2,X0,X1] : (v4_relat_1(X2,X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v4_relat_1(X2,X0)) )),
% 0.92/0.67    inference(duplicate_literal_removal,[],[f56])).
% 0.92/0.67  fof(f56,plain,(
% 0.92/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | v4_relat_1(X2,X1) | ~v1_relat_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 0.92/0.67    inference(resolution,[],[f49,f32])).
% 0.92/0.67  fof(f32,plain,(
% 0.92/0.67    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.92/0.67    inference(cnf_transformation,[],[f25])).
% 0.92/0.67  fof(f25,plain,(
% 0.92/0.67    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.92/0.67    inference(nnf_transformation,[],[f14])).
% 0.92/0.67  fof(f14,plain,(
% 0.92/0.67    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.92/0.67    inference(ennf_transformation,[],[f3])).
% 0.92/0.67  fof(f3,axiom,(
% 0.92/0.67    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.92/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.92/0.67  fof(f49,plain,(
% 0.92/0.67    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(X0,X1) | v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.92/0.67    inference(resolution,[],[f37,f33])).
% 0.92/0.67  fof(f33,plain,(
% 0.92/0.67    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.92/0.67    inference(cnf_transformation,[],[f25])).
% 0.92/0.67  fof(f37,plain,(
% 0.92/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.92/0.67    inference(cnf_transformation,[],[f19])).
% 0.92/0.67  fof(f19,plain,(
% 0.92/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.92/0.67    inference(flattening,[],[f18])).
% 0.92/0.67  fof(f18,plain,(
% 0.92/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.92/0.67    inference(ennf_transformation,[],[f1])).
% 0.92/0.67  fof(f1,axiom,(
% 0.92/0.67    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.92/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.92/0.67  % SZS output end Proof for theBenchmark
% 0.92/0.67  % (21469)------------------------------
% 0.92/0.67  % (21469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.92/0.67  % (21469)Termination reason: Refutation
% 0.92/0.67  
% 0.92/0.67  % (21469)Memory used [KB]: 6140
% 0.92/0.67  % (21469)Time elapsed: 0.085 s
% 0.92/0.67  % (21469)------------------------------
% 0.92/0.67  % (21469)------------------------------
% 0.92/0.67  % (21238)Success in time 0.312 s
%------------------------------------------------------------------------------

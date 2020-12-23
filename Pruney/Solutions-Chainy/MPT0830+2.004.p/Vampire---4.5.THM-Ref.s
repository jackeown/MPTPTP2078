%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:45 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   42 (  77 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   83 ( 163 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f64,f109,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f109,plain,(
    ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ),
    inference(unit_resulting_resolution,[],[f59,f66,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(f66,plain,(
    ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f56,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ~ r1_tarski(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2)) ),
    inference(forward_demodulation,[],[f54,f47])).

fof(f47,plain,(
    ! [X0] : k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f33,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

fof(f54,plain,(
    ~ r1_tarski(k5_relset_1(sK0,sK2,sK3,sK1),k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f42])).

fof(f34,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f46,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f46,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f33,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f64,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f48,f58,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f58,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK3,X0),sK3) ),
    inference(unit_resulting_resolution,[],[f46,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f48,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f33,f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:21:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (798261248)
% 0.14/0.37  ipcrm: permission denied for id (801177601)
% 0.14/0.37  ipcrm: permission denied for id (801275908)
% 0.14/0.37  ipcrm: permission denied for id (801341446)
% 0.14/0.37  ipcrm: permission denied for id (801406984)
% 0.14/0.38  ipcrm: permission denied for id (801439753)
% 0.14/0.38  ipcrm: permission denied for id (801472522)
% 0.14/0.38  ipcrm: permission denied for id (798425100)
% 0.14/0.38  ipcrm: permission denied for id (801538061)
% 0.14/0.38  ipcrm: permission denied for id (801570830)
% 0.14/0.38  ipcrm: permission denied for id (801636368)
% 0.14/0.39  ipcrm: permission denied for id (798490641)
% 0.14/0.39  ipcrm: permission denied for id (801669138)
% 0.14/0.39  ipcrm: permission denied for id (801701907)
% 0.14/0.39  ipcrm: permission denied for id (798588949)
% 0.14/0.39  ipcrm: permission denied for id (801767446)
% 0.14/0.40  ipcrm: permission denied for id (798654490)
% 0.14/0.40  ipcrm: permission denied for id (801931292)
% 0.20/0.40  ipcrm: permission denied for id (798752799)
% 0.20/0.40  ipcrm: permission denied for id (798818336)
% 0.20/0.40  ipcrm: permission denied for id (802029601)
% 0.20/0.41  ipcrm: permission denied for id (798883875)
% 0.20/0.41  ipcrm: permission denied for id (798916645)
% 0.20/0.41  ipcrm: permission denied for id (798949414)
% 0.20/0.41  ipcrm: permission denied for id (802160680)
% 0.20/0.42  ipcrm: permission denied for id (802226218)
% 0.20/0.42  ipcrm: permission denied for id (802291756)
% 0.20/0.42  ipcrm: permission denied for id (799080493)
% 0.20/0.42  ipcrm: permission denied for id (799113262)
% 0.20/0.42  ipcrm: permission denied for id (799146031)
% 0.20/0.42  ipcrm: permission denied for id (802324528)
% 0.20/0.42  ipcrm: permission denied for id (802390065)
% 0.20/0.43  ipcrm: permission denied for id (802422834)
% 0.20/0.43  ipcrm: permission denied for id (802488372)
% 0.20/0.43  ipcrm: permission denied for id (799309877)
% 0.20/0.43  ipcrm: permission denied for id (799408184)
% 0.20/0.44  ipcrm: permission denied for id (799473721)
% 0.20/0.44  ipcrm: permission denied for id (802586682)
% 0.20/0.44  ipcrm: permission denied for id (802619451)
% 0.20/0.44  ipcrm: permission denied for id (802652220)
% 0.20/0.44  ipcrm: permission denied for id (802717758)
% 0.20/0.45  ipcrm: permission denied for id (799604799)
% 0.20/0.45  ipcrm: permission denied for id (799637568)
% 0.20/0.45  ipcrm: permission denied for id (802848835)
% 0.20/0.45  ipcrm: permission denied for id (799703108)
% 0.20/0.45  ipcrm: permission denied for id (799735877)
% 0.20/0.46  ipcrm: permission denied for id (799768646)
% 0.20/0.46  ipcrm: permission denied for id (799801415)
% 0.20/0.46  ipcrm: permission denied for id (799834184)
% 0.20/0.46  ipcrm: permission denied for id (802881609)
% 0.20/0.46  ipcrm: permission denied for id (799899723)
% 0.20/0.47  ipcrm: permission denied for id (799932492)
% 0.20/0.47  ipcrm: permission denied for id (799965261)
% 0.20/0.47  ipcrm: permission denied for id (802947150)
% 0.20/0.47  ipcrm: permission denied for id (802979919)
% 0.20/0.47  ipcrm: permission denied for id (800030800)
% 0.20/0.47  ipcrm: permission denied for id (800063569)
% 0.20/0.48  ipcrm: permission denied for id (800096338)
% 0.20/0.48  ipcrm: permission denied for id (800129107)
% 0.20/0.48  ipcrm: permission denied for id (803012692)
% 0.20/0.48  ipcrm: permission denied for id (800194646)
% 0.20/0.48  ipcrm: permission denied for id (803111000)
% 0.20/0.49  ipcrm: permission denied for id (800227418)
% 0.20/0.49  ipcrm: permission denied for id (800260188)
% 0.20/0.49  ipcrm: permission denied for id (803209309)
% 0.20/0.49  ipcrm: permission denied for id (803242078)
% 0.20/0.49  ipcrm: permission denied for id (800358495)
% 0.20/0.50  ipcrm: permission denied for id (803307617)
% 0.20/0.50  ipcrm: permission denied for id (800391266)
% 0.20/0.50  ipcrm: permission denied for id (803340387)
% 0.20/0.50  ipcrm: permission denied for id (800424036)
% 0.20/0.50  ipcrm: permission denied for id (803373157)
% 0.20/0.51  ipcrm: permission denied for id (800587880)
% 0.20/0.51  ipcrm: permission denied for id (800620649)
% 0.20/0.51  ipcrm: permission denied for id (803471466)
% 0.20/0.51  ipcrm: permission denied for id (803504235)
% 0.20/0.51  ipcrm: permission denied for id (803537004)
% 0.20/0.52  ipcrm: permission denied for id (803569773)
% 0.20/0.52  ipcrm: permission denied for id (803602542)
% 0.20/0.52  ipcrm: permission denied for id (803635311)
% 0.20/0.52  ipcrm: permission denied for id (800850032)
% 0.20/0.52  ipcrm: permission denied for id (800882802)
% 0.20/0.52  ipcrm: permission denied for id (803700851)
% 0.20/0.53  ipcrm: permission denied for id (800915572)
% 0.20/0.53  ipcrm: permission denied for id (803799159)
% 0.20/0.53  ipcrm: permission denied for id (800981112)
% 0.20/0.53  ipcrm: permission denied for id (803831929)
% 0.20/0.53  ipcrm: permission denied for id (803864698)
% 0.20/0.54  ipcrm: permission denied for id (801046651)
% 0.20/0.54  ipcrm: permission denied for id (801112189)
% 0.20/0.54  ipcrm: permission denied for id (803930238)
% 0.20/0.54  ipcrm: permission denied for id (803963007)
% 0.79/0.63  % (32429)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.98/0.65  % (32431)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.98/0.65  % (32440)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.98/0.66  % (32429)Refutation not found, incomplete strategy% (32429)------------------------------
% 0.98/0.66  % (32429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.98/0.66  % (32421)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.98/0.66  % (32428)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.98/0.66  % (32437)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.98/0.66  % (32430)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.98/0.66  % (32429)Termination reason: Refutation not found, incomplete strategy
% 0.98/0.66  
% 0.98/0.66  % (32429)Memory used [KB]: 10490
% 0.98/0.66  % (32429)Time elapsed: 0.067 s
% 0.98/0.66  % (32429)------------------------------
% 0.98/0.66  % (32429)------------------------------
% 0.98/0.66  % (32444)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.98/0.66  % (32433)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.98/0.66  % (32424)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.98/0.66  % (32434)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.98/0.66  % (32425)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.98/0.66  % (32427)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.98/0.67  % (32438)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.98/0.67  % (32431)Refutation not found, incomplete strategy% (32431)------------------------------
% 0.98/0.67  % (32431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.98/0.67  % (32426)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.98/0.67  % (32432)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.98/0.67  % (32427)Refutation not found, incomplete strategy% (32427)------------------------------
% 0.98/0.67  % (32427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.98/0.67  % (32427)Termination reason: Refutation not found, incomplete strategy
% 0.98/0.67  
% 0.98/0.67  % (32427)Memory used [KB]: 10746
% 0.98/0.67  % (32427)Time elapsed: 0.082 s
% 0.98/0.67  % (32427)------------------------------
% 0.98/0.67  % (32427)------------------------------
% 0.98/0.67  % (32437)Refutation found. Thanks to Tanya!
% 0.98/0.67  % SZS status Theorem for theBenchmark
% 0.98/0.67  % SZS output start Proof for theBenchmark
% 0.98/0.67  fof(f175,plain,(
% 0.98/0.67    $false),
% 0.98/0.67    inference(unit_resulting_resolution,[],[f64,f109,f42])).
% 0.98/0.67  fof(f42,plain,(
% 0.98/0.67    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.98/0.67    inference(cnf_transformation,[],[f32])).
% 0.98/0.67  fof(f32,plain,(
% 0.98/0.67    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.98/0.67    inference(nnf_transformation,[],[f2])).
% 0.98/0.67  fof(f2,axiom,(
% 0.98/0.67    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.98/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.98/0.67  fof(f109,plain,(
% 0.98/0.67    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 0.98/0.67    inference(unit_resulting_resolution,[],[f59,f66,f43])).
% 0.98/0.67  fof(f43,plain,(
% 0.98/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.98/0.67    inference(cnf_transformation,[],[f27])).
% 0.98/0.67  fof(f27,plain,(
% 0.98/0.67    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.98/0.67    inference(flattening,[],[f26])).
% 0.98/0.67  fof(f26,plain,(
% 0.98/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.98/0.67    inference(ennf_transformation,[],[f14])).
% 0.98/0.67  fof(f14,axiom,(
% 0.98/0.67    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.98/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).
% 0.98/0.67  fof(f66,plain,(
% 0.98/0.67    ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.98/0.67    inference(unit_resulting_resolution,[],[f56,f41])).
% 0.98/0.67  fof(f41,plain,(
% 0.98/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.98/0.67    inference(cnf_transformation,[],[f32])).
% 0.98/0.67  fof(f56,plain,(
% 0.98/0.67    ~r1_tarski(k7_relat_1(sK3,sK1),k2_zfmisc_1(sK1,sK2))),
% 0.98/0.67    inference(forward_demodulation,[],[f54,f47])).
% 0.98/0.67  fof(f47,plain,(
% 0.98/0.67    ( ! [X0] : (k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.98/0.67    inference(unit_resulting_resolution,[],[f33,f35])).
% 0.98/0.67  fof(f35,plain,(
% 0.98/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.98/0.67    inference(cnf_transformation,[],[f18])).
% 0.98/0.67  fof(f18,plain,(
% 0.98/0.67    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.98/0.67    inference(ennf_transformation,[],[f11])).
% 0.98/0.67  fof(f11,axiom,(
% 0.98/0.67    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.98/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.98/0.67  fof(f33,plain,(
% 0.98/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.98/0.67    inference(cnf_transformation,[],[f31])).
% 0.98/0.67  fof(f31,plain,(
% 0.98/0.67    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.98/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f30])).
% 0.98/0.67  fof(f30,plain,(
% 0.98/0.67    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 0.98/0.67    introduced(choice_axiom,[])).
% 0.98/0.67  fof(f17,plain,(
% 0.98/0.67    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.98/0.67    inference(ennf_transformation,[],[f16])).
% 0.98/0.67  fof(f16,negated_conjecture,(
% 0.98/0.67    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.98/0.67    inference(negated_conjecture,[],[f15])).
% 0.98/0.67  fof(f15,conjecture,(
% 0.98/0.67    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.98/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).
% 0.98/0.67  fof(f54,plain,(
% 0.98/0.67    ~r1_tarski(k5_relset_1(sK0,sK2,sK3,sK1),k2_zfmisc_1(sK1,sK2))),
% 0.98/0.67    inference(unit_resulting_resolution,[],[f34,f42])).
% 0.98/0.67  fof(f34,plain,(
% 0.98/0.67    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.98/0.67    inference(cnf_transformation,[],[f31])).
% 0.98/0.67  fof(f59,plain,(
% 0.98/0.67    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)) )),
% 0.98/0.67    inference(unit_resulting_resolution,[],[f46,f38])).
% 0.98/0.67  fof(f38,plain,(
% 0.98/0.67    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.98/0.67    inference(cnf_transformation,[],[f22])).
% 0.98/0.67  fof(f22,plain,(
% 0.98/0.67    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.98/0.67    inference(ennf_transformation,[],[f4])).
% 0.98/0.67  fof(f4,axiom,(
% 0.98/0.67    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.98/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.98/0.67  fof(f46,plain,(
% 0.98/0.67    v1_relat_1(sK3)),
% 0.98/0.67    inference(unit_resulting_resolution,[],[f33,f44])).
% 0.98/0.67  fof(f44,plain,(
% 0.98/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.98/0.67    inference(cnf_transformation,[],[f28])).
% 0.98/0.67  fof(f28,plain,(
% 0.98/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.98/0.67    inference(ennf_transformation,[],[f8])).
% 0.98/0.67  fof(f8,axiom,(
% 0.98/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.98/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.98/0.67  fof(f64,plain,(
% 0.98/0.67    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK2))) )),
% 0.98/0.67    inference(unit_resulting_resolution,[],[f48,f58,f40])).
% 0.98/0.67  fof(f40,plain,(
% 0.98/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.98/0.67    inference(cnf_transformation,[],[f25])).
% 0.98/0.67  fof(f25,plain,(
% 0.98/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.98/0.67    inference(flattening,[],[f24])).
% 0.98/0.67  fof(f24,plain,(
% 0.98/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.98/0.67    inference(ennf_transformation,[],[f1])).
% 0.98/0.67  fof(f1,axiom,(
% 0.98/0.67    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.98/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.98/0.67  fof(f58,plain,(
% 0.98/0.67    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),sK3)) )),
% 0.98/0.67    inference(unit_resulting_resolution,[],[f46,f39])).
% 0.98/0.67  fof(f39,plain,(
% 0.98/0.67    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.98/0.67    inference(cnf_transformation,[],[f23])).
% 0.98/0.67  fof(f23,plain,(
% 0.98/0.67    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.98/0.67    inference(ennf_transformation,[],[f5])).
% 0.98/0.67  fof(f5,axiom,(
% 0.98/0.67    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.98/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.98/0.67  fof(f48,plain,(
% 0.98/0.67    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))),
% 0.98/0.67    inference(unit_resulting_resolution,[],[f33,f41])).
% 0.98/0.67  % SZS output end Proof for theBenchmark
% 0.98/0.67  % (32437)------------------------------
% 0.98/0.67  % (32437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.98/0.67  % (32437)Termination reason: Refutation
% 0.98/0.67  
% 0.98/0.67  % (32437)Memory used [KB]: 1791
% 0.98/0.67  % (32437)Time elapsed: 0.084 s
% 0.98/0.67  % (32437)------------------------------
% 0.98/0.67  % (32437)------------------------------
% 0.98/0.67  % (32441)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.98/0.67  % (32423)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.98/0.67  % (32431)Termination reason: Refutation not found, incomplete strategy
% 0.98/0.67  
% 0.98/0.67  % (32431)Memory used [KB]: 10618
% 0.98/0.67  % (32431)Time elapsed: 0.081 s
% 0.98/0.67  % (32431)------------------------------
% 0.98/0.67  % (32431)------------------------------
% 0.98/0.67  % (32436)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.98/0.68  % (32443)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.98/0.68  % (32435)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.98/0.68  % (32251)Success in time 0.318 s
%------------------------------------------------------------------------------

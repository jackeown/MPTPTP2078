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
% DateTime   : Thu Dec  3 12:58:02 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   41 (  68 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 163 expanded)
%              Number of equality atoms :   22 (  42 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f50,plain,(
    $false ),
    inference(global_subsumption,[],[f46,f49])).

fof(f49,plain,(
    k1_xboole_0 = k7_relat_1(sK3,sK1) ),
    inference(resolution,[],[f48,f21])).

fof(f21,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_xboole_0(X1,X2)
         => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_xboole_0(X1,X2)
       => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

% (16416)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
fof(f48,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | k1_xboole_0 = k7_relat_1(sK3,X0) ) ),
    inference(global_subsumption,[],[f33,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | ~ v1_relat_1(sK3)
      | k1_xboole_0 = k7_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f45,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,X1) = k1_xboole_0
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k7_relat_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f45,plain,(
    ! [X2] :
      ( r1_xboole_0(X2,k1_relat_1(sK3))
      | ~ r1_xboole_0(X2,sK2) ) ),
    inference(superposition,[],[f27,f41])).

fof(f41,plain,(
    sK2 = k2_xboole_0(k1_relat_1(sK3),sK2) ),
    inference(global_subsumption,[],[f33,f40])).

fof(f40,plain,
    ( ~ v1_relat_1(sK3)
    | sK2 = k2_xboole_0(k1_relat_1(sK3),sK2) ),
    inference(resolution,[],[f35,f37])).

fof(f37,plain,(
    v4_relat_1(sK3,sK2) ),
    inference(resolution,[],[f31,f20])).

fof(f20,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f35,plain,(
    ! [X2,X3] :
      ( ~ v4_relat_1(X2,X3)
      | ~ v1_relat_1(X2)
      | k2_xboole_0(k1_relat_1(X2),X3) = X3 ) ),
    inference(resolution,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

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

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f33,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f30,f20])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f46,plain,(
    k1_xboole_0 != k7_relat_1(sK3,sK1) ),
    inference(superposition,[],[f22,f42])).

fof(f42,plain,(
    ! [X0] : k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(resolution,[],[f32,f20])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f22,plain,(
    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:18:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (819134465)
% 0.13/0.37  ipcrm: permission denied for id (819167234)
% 0.13/0.38  ipcrm: permission denied for id (824147971)
% 0.13/0.38  ipcrm: permission denied for id (824180740)
% 0.13/0.38  ipcrm: permission denied for id (819200005)
% 0.13/0.38  ipcrm: permission denied for id (819232774)
% 0.13/0.38  ipcrm: permission denied for id (820805639)
% 0.13/0.38  ipcrm: permission denied for id (824213512)
% 0.13/0.38  ipcrm: permission denied for id (820871177)
% 0.13/0.38  ipcrm: permission denied for id (820903946)
% 0.13/0.38  ipcrm: permission denied for id (820936715)
% 0.13/0.39  ipcrm: permission denied for id (821002253)
% 0.13/0.39  ipcrm: permission denied for id (824311823)
% 0.13/0.39  ipcrm: permission denied for id (824344592)
% 0.13/0.39  ipcrm: permission denied for id (824410130)
% 0.13/0.39  ipcrm: permission denied for id (819331091)
% 0.13/0.39  ipcrm: permission denied for id (819363861)
% 0.13/0.39  ipcrm: permission denied for id (819396630)
% 0.13/0.39  ipcrm: permission denied for id (819429399)
% 0.13/0.40  ipcrm: permission denied for id (824475672)
% 0.13/0.40  ipcrm: permission denied for id (824508441)
% 0.13/0.40  ipcrm: permission denied for id (821297178)
% 0.13/0.40  ipcrm: permission denied for id (821329947)
% 0.13/0.40  ipcrm: permission denied for id (819462172)
% 0.13/0.40  ipcrm: permission denied for id (821362717)
% 0.13/0.40  ipcrm: permission denied for id (821395486)
% 0.13/0.40  ipcrm: permission denied for id (821461024)
% 0.13/0.40  ipcrm: permission denied for id (821526562)
% 0.21/0.41  ipcrm: permission denied for id (819593251)
% 0.21/0.41  ipcrm: permission denied for id (821592100)
% 0.21/0.41  ipcrm: permission denied for id (819658791)
% 0.21/0.41  ipcrm: permission denied for id (821690408)
% 0.21/0.41  ipcrm: permission denied for id (821723177)
% 0.21/0.41  ipcrm: permission denied for id (821755946)
% 0.21/0.41  ipcrm: permission denied for id (821788715)
% 0.21/0.41  ipcrm: permission denied for id (821821484)
% 0.21/0.41  ipcrm: permission denied for id (824672301)
% 0.21/0.42  ipcrm: permission denied for id (821887022)
% 0.21/0.42  ipcrm: permission denied for id (821919791)
% 0.21/0.42  ipcrm: permission denied for id (821952560)
% 0.21/0.42  ipcrm: permission denied for id (824737842)
% 0.21/0.42  ipcrm: permission denied for id (822050867)
% 0.21/0.42  ipcrm: permission denied for id (824770612)
% 0.21/0.42  ipcrm: permission denied for id (819789877)
% 0.21/0.42  ipcrm: permission denied for id (822116406)
% 0.21/0.42  ipcrm: permission denied for id (822149175)
% 0.21/0.42  ipcrm: permission denied for id (822181944)
% 0.21/0.43  ipcrm: permission denied for id (822214713)
% 0.21/0.43  ipcrm: permission denied for id (824803386)
% 0.21/0.43  ipcrm: permission denied for id (819855419)
% 0.21/0.43  ipcrm: permission denied for id (824836156)
% 0.21/0.43  ipcrm: permission denied for id (819888189)
% 0.21/0.43  ipcrm: permission denied for id (819953726)
% 0.21/0.43  ipcrm: permission denied for id (819986495)
% 0.21/0.43  ipcrm: permission denied for id (822411330)
% 0.21/0.43  ipcrm: permission denied for id (822444099)
% 0.21/0.44  ipcrm: permission denied for id (824934468)
% 0.21/0.44  ipcrm: permission denied for id (824967237)
% 0.21/0.44  ipcrm: permission denied for id (825000006)
% 0.21/0.44  ipcrm: permission denied for id (820117575)
% 0.21/0.44  ipcrm: permission denied for id (820150346)
% 0.21/0.44  ipcrm: permission denied for id (822706252)
% 0.21/0.44  ipcrm: permission denied for id (822739021)
% 0.21/0.44  ipcrm: permission denied for id (820183118)
% 0.21/0.45  ipcrm: permission denied for id (825131087)
% 0.21/0.45  ipcrm: permission denied for id (822804560)
% 0.21/0.45  ipcrm: permission denied for id (820248657)
% 0.21/0.45  ipcrm: permission denied for id (825163858)
% 0.21/0.45  ipcrm: permission denied for id (822870099)
% 0.21/0.45  ipcrm: permission denied for id (822902868)
% 0.21/0.45  ipcrm: permission denied for id (825196629)
% 0.21/0.45  ipcrm: permission denied for id (823001175)
% 0.21/0.45  ipcrm: permission denied for id (820281432)
% 0.21/0.46  ipcrm: permission denied for id (820346970)
% 0.21/0.46  ipcrm: permission denied for id (823066715)
% 0.21/0.46  ipcrm: permission denied for id (823099484)
% 0.21/0.46  ipcrm: permission denied for id (825393246)
% 0.21/0.46  ipcrm: permission denied for id (823197791)
% 0.21/0.46  ipcrm: permission denied for id (825426016)
% 0.21/0.46  ipcrm: permission denied for id (823296098)
% 0.21/0.46  ipcrm: permission denied for id (825524324)
% 0.21/0.46  ipcrm: permission denied for id (820379749)
% 0.21/0.47  ipcrm: permission denied for id (823394406)
% 0.21/0.47  ipcrm: permission denied for id (825557095)
% 0.21/0.47  ipcrm: permission denied for id (823459944)
% 0.21/0.47  ipcrm: permission denied for id (825589865)
% 0.21/0.47  ipcrm: permission denied for id (823525482)
% 0.21/0.47  ipcrm: permission denied for id (825622635)
% 0.21/0.47  ipcrm: permission denied for id (823623789)
% 0.21/0.47  ipcrm: permission denied for id (820412527)
% 0.21/0.47  ipcrm: permission denied for id (820445296)
% 0.21/0.47  ipcrm: permission denied for id (823689329)
% 0.21/0.47  ipcrm: permission denied for id (825720946)
% 0.21/0.48  ipcrm: permission denied for id (823787636)
% 0.21/0.48  ipcrm: permission denied for id (820543605)
% 0.21/0.48  ipcrm: permission denied for id (823820406)
% 0.21/0.48  ipcrm: permission denied for id (820576375)
% 0.21/0.48  ipcrm: permission denied for id (825786488)
% 0.21/0.48  ipcrm: permission denied for id (820609145)
% 0.21/0.48  ipcrm: permission denied for id (823918714)
% 0.21/0.48  ipcrm: permission denied for id (825819259)
% 0.21/0.49  ipcrm: permission denied for id (825852028)
% 0.21/0.49  ipcrm: permission denied for id (825884797)
% 0.21/0.49  ipcrm: permission denied for id (825917566)
% 0.21/0.49  ipcrm: permission denied for id (824082559)
% 0.21/0.57  % (16404)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.58  % (16411)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.59  % (16408)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.59  % (16401)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.59  % (16400)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.60  % (16396)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.60  % (16404)Refutation not found, incomplete strategy% (16404)------------------------------
% 0.21/0.60  % (16404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (16404)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (16404)Memory used [KB]: 10490
% 0.21/0.60  % (16404)Time elapsed: 0.081 s
% 0.21/0.60  % (16404)------------------------------
% 0.21/0.60  % (16404)------------------------------
% 1.04/0.61  % (16415)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.04/0.61  % (16402)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.04/0.61  % (16398)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.04/0.62  % (16408)Refutation found. Thanks to Tanya!
% 1.04/0.62  % SZS status Theorem for theBenchmark
% 1.04/0.62  % SZS output start Proof for theBenchmark
% 1.04/0.62  fof(f50,plain,(
% 1.04/0.62    $false),
% 1.04/0.62    inference(global_subsumption,[],[f46,f49])).
% 1.04/0.62  fof(f49,plain,(
% 1.04/0.62    k1_xboole_0 = k7_relat_1(sK3,sK1)),
% 1.04/0.62    inference(resolution,[],[f48,f21])).
% 1.04/0.62  fof(f21,plain,(
% 1.04/0.62    r1_xboole_0(sK1,sK2)),
% 1.04/0.62    inference(cnf_transformation,[],[f12])).
% 1.04/0.62  fof(f12,plain,(
% 1.04/0.62    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 1.04/0.62    inference(flattening,[],[f11])).
% 1.04/0.62  fof(f11,plain,(
% 1.04/0.62    ? [X0,X1,X2,X3] : ((k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 1.04/0.62    inference(ennf_transformation,[],[f9])).
% 1.04/0.62  fof(f9,negated_conjecture,(
% 1.04/0.62    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 1.04/0.62    inference(negated_conjecture,[],[f8])).
% 1.04/0.62  fof(f8,conjecture,(
% 1.04/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 1.04/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).
% 1.04/0.62  % (16416)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.04/0.62  fof(f48,plain,(
% 1.04/0.62    ( ! [X0] : (~r1_xboole_0(X0,sK2) | k1_xboole_0 = k7_relat_1(sK3,X0)) )),
% 1.04/0.62    inference(global_subsumption,[],[f33,f47])).
% 1.04/0.62  fof(f47,plain,(
% 1.04/0.62    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~v1_relat_1(sK3) | k1_xboole_0 = k7_relat_1(sK3,X0)) )),
% 1.04/0.62    inference(resolution,[],[f45,f23])).
% 1.04/0.62  fof(f23,plain,(
% 1.04/0.62    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = k1_xboole_0) )),
% 1.04/0.62    inference(cnf_transformation,[],[f13])).
% 1.04/0.62  fof(f13,plain,(
% 1.04/0.62    ! [X0] : (! [X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.04/0.62    inference(ennf_transformation,[],[f4])).
% 1.04/0.62  fof(f4,axiom,(
% 1.04/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k7_relat_1(X0,X1) = k1_xboole_0))),
% 1.04/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 1.04/0.62  fof(f45,plain,(
% 1.04/0.62    ( ! [X2] : (r1_xboole_0(X2,k1_relat_1(sK3)) | ~r1_xboole_0(X2,sK2)) )),
% 1.04/0.62    inference(superposition,[],[f27,f41])).
% 1.04/0.62  fof(f41,plain,(
% 1.04/0.62    sK2 = k2_xboole_0(k1_relat_1(sK3),sK2)),
% 1.04/0.62    inference(global_subsumption,[],[f33,f40])).
% 1.04/0.62  fof(f40,plain,(
% 1.04/0.62    ~v1_relat_1(sK3) | sK2 = k2_xboole_0(k1_relat_1(sK3),sK2)),
% 1.04/0.62    inference(resolution,[],[f35,f37])).
% 1.04/0.62  fof(f37,plain,(
% 1.04/0.62    v4_relat_1(sK3,sK2)),
% 1.04/0.62    inference(resolution,[],[f31,f20])).
% 1.04/0.62  fof(f20,plain,(
% 1.04/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.04/0.62    inference(cnf_transformation,[],[f12])).
% 1.04/0.62  fof(f31,plain,(
% 1.04/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.04/0.62    inference(cnf_transformation,[],[f18])).
% 1.04/0.62  fof(f18,plain,(
% 1.04/0.62    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.04/0.62    inference(ennf_transformation,[],[f10])).
% 1.04/0.62  fof(f10,plain,(
% 1.04/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.04/0.62    inference(pure_predicate_removal,[],[f6])).
% 1.04/0.62  fof(f6,axiom,(
% 1.04/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.04/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.04/0.62  fof(f35,plain,(
% 1.04/0.62    ( ! [X2,X3] : (~v4_relat_1(X2,X3) | ~v1_relat_1(X2) | k2_xboole_0(k1_relat_1(X2),X3) = X3) )),
% 1.04/0.62    inference(resolution,[],[f25,f26])).
% 1.04/0.62  fof(f26,plain,(
% 1.04/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.04/0.62    inference(cnf_transformation,[],[f15])).
% 1.04/0.62  fof(f15,plain,(
% 1.04/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.04/0.62    inference(ennf_transformation,[],[f1])).
% 1.04/0.62  fof(f1,axiom,(
% 1.04/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.04/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.04/0.62  fof(f25,plain,(
% 1.04/0.62    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 1.04/0.62    inference(cnf_transformation,[],[f14])).
% 1.04/0.62  fof(f14,plain,(
% 1.04/0.62    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.04/0.62    inference(ennf_transformation,[],[f3])).
% 1.04/0.62  fof(f3,axiom,(
% 1.04/0.62    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.04/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.04/0.62  fof(f27,plain,(
% 1.04/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 1.04/0.62    inference(cnf_transformation,[],[f16])).
% 1.04/0.62  fof(f16,plain,(
% 1.04/0.62    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.04/0.62    inference(ennf_transformation,[],[f2])).
% 1.04/0.62  fof(f2,axiom,(
% 1.04/0.62    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.04/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.04/0.62  fof(f33,plain,(
% 1.04/0.62    v1_relat_1(sK3)),
% 1.04/0.62    inference(resolution,[],[f30,f20])).
% 1.04/0.62  fof(f30,plain,(
% 1.04/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.04/0.62    inference(cnf_transformation,[],[f17])).
% 1.04/0.62  fof(f17,plain,(
% 1.04/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.04/0.62    inference(ennf_transformation,[],[f5])).
% 1.04/0.62  fof(f5,axiom,(
% 1.04/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.04/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.04/0.62  fof(f46,plain,(
% 1.04/0.62    k1_xboole_0 != k7_relat_1(sK3,sK1)),
% 1.04/0.62    inference(superposition,[],[f22,f42])).
% 1.04/0.62  fof(f42,plain,(
% 1.04/0.62    ( ! [X0] : (k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 1.04/0.62    inference(resolution,[],[f32,f20])).
% 1.04/0.62  fof(f32,plain,(
% 1.04/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.04/0.62    inference(cnf_transformation,[],[f19])).
% 1.04/0.62  fof(f19,plain,(
% 1.04/0.62    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.04/0.62    inference(ennf_transformation,[],[f7])).
% 1.04/0.62  fof(f7,axiom,(
% 1.04/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.04/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 1.04/0.62  fof(f22,plain,(
% 1.04/0.62    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)),
% 1.04/0.62    inference(cnf_transformation,[],[f12])).
% 1.04/0.62  % SZS output end Proof for theBenchmark
% 1.04/0.62  % (16408)------------------------------
% 1.04/0.62  % (16408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.04/0.62  % (16408)Termination reason: Refutation
% 1.04/0.62  
% 1.04/0.62  % (16408)Memory used [KB]: 10618
% 1.04/0.62  % (16408)Time elapsed: 0.089 s
% 1.04/0.62  % (16408)------------------------------
% 1.04/0.62  % (16408)------------------------------
% 1.17/0.62  % (16248)Success in time 0.253 s
%------------------------------------------------------------------------------

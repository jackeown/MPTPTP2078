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
% DateTime   : Thu Dec  3 12:56:57 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 107 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 290 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(subsumption_resolution,[],[f94,f74])).

fof(f74,plain,(
    r2_relset_1(sK1,sK0,sK3,sK3) ),
    inference(subsumption_resolution,[],[f49,f45])).

fof(f45,plain,(
    ~ sP4(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f27,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP4(X1,X0) ) ),
    inference(general_splitting,[],[f30,f39_D])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP4(X1,X0) ) ),
    inference(cnf_transformation,[],[f39_D])).

fof(f39_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X1,X2,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    <=> ~ sP4(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

fof(f49,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | sP4(sK0,sK1) ),
    inference(resolution,[],[f27,f39])).

fof(f94,plain,(
    ~ r2_relset_1(sK1,sK0,sK3,sK3) ),
    inference(backward_demodulation,[],[f85,f75])).

fof(f75,plain,(
    sK3 = k7_relat_1(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f46,f64,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f64,plain,(
    r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(unit_resulting_resolution,[],[f58,f42])).

fof(f42,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | r1_tarski(X1,sK2) ) ),
    inference(resolution,[],[f28,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f28,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(unit_resulting_resolution,[],[f46,f43,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f43,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f27,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f46,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f38,f27,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f85,plain,(
    ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) ),
    inference(backward_demodulation,[],[f29,f44])).

fof(f44,plain,(
    ! [X0] : k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f27,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f29,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:26:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (812843008)
% 0.14/0.37  ipcrm: permission denied for id (815529987)
% 0.14/0.37  ipcrm: permission denied for id (815562756)
% 0.22/0.37  ipcrm: permission denied for id (815595525)
% 0.22/0.38  ipcrm: permission denied for id (815628294)
% 0.22/0.38  ipcrm: permission denied for id (815661063)
% 0.22/0.38  ipcrm: permission denied for id (815693832)
% 0.22/0.38  ipcrm: permission denied for id (818610185)
% 0.22/0.38  ipcrm: permission denied for id (813006858)
% 0.22/0.38  ipcrm: permission denied for id (813039627)
% 0.22/0.38  ipcrm: permission denied for id (815759372)
% 0.22/0.38  ipcrm: permission denied for id (818642957)
% 0.22/0.39  ipcrm: permission denied for id (819986446)
% 0.22/0.39  ipcrm: permission denied for id (815857679)
% 0.22/0.39  ipcrm: permission denied for id (813170704)
% 0.22/0.39  ipcrm: permission denied for id (818708497)
% 0.22/0.39  ipcrm: permission denied for id (813236242)
% 0.22/0.39  ipcrm: permission denied for id (815923219)
% 0.22/0.39  ipcrm: permission denied for id (815955988)
% 0.22/0.39  ipcrm: permission denied for id (818741269)
% 0.22/0.40  ipcrm: permission denied for id (816021526)
% 0.22/0.40  ipcrm: permission denied for id (816054295)
% 0.22/0.40  ipcrm: permission denied for id (816087064)
% 0.22/0.40  ipcrm: permission denied for id (818774041)
% 0.22/0.40  ipcrm: permission denied for id (816152602)
% 0.22/0.40  ipcrm: permission denied for id (816185371)
% 0.22/0.40  ipcrm: permission denied for id (820019228)
% 0.22/0.41  ipcrm: permission denied for id (820051997)
% 0.22/0.41  ipcrm: permission denied for id (816283678)
% 0.22/0.41  ipcrm: permission denied for id (820084767)
% 0.22/0.41  ipcrm: permission denied for id (813432864)
% 0.22/0.41  ipcrm: permission denied for id (813465633)
% 0.22/0.41  ipcrm: permission denied for id (816349218)
% 0.22/0.41  ipcrm: permission denied for id (818905123)
% 0.22/0.41  ipcrm: permission denied for id (816414756)
% 0.22/0.42  ipcrm: permission denied for id (816447525)
% 0.22/0.42  ipcrm: permission denied for id (818937894)
% 0.22/0.42  ipcrm: permission denied for id (816513063)
% 0.22/0.42  ipcrm: permission denied for id (818970664)
% 0.22/0.42  ipcrm: permission denied for id (813596713)
% 0.22/0.42  ipcrm: permission denied for id (813629482)
% 0.22/0.42  ipcrm: permission denied for id (816578603)
% 0.22/0.42  ipcrm: permission denied for id (816611372)
% 0.22/0.43  ipcrm: permission denied for id (813727789)
% 0.22/0.43  ipcrm: permission denied for id (819003438)
% 0.22/0.43  ipcrm: permission denied for id (820117551)
% 0.22/0.43  ipcrm: permission denied for id (816709680)
% 0.22/0.43  ipcrm: permission denied for id (816742449)
% 0.22/0.43  ipcrm: permission denied for id (819068978)
% 0.22/0.43  ipcrm: permission denied for id (820740147)
% 0.22/0.43  ipcrm: permission denied for id (813793332)
% 0.22/0.44  ipcrm: permission denied for id (820183093)
% 0.22/0.44  ipcrm: permission denied for id (816873526)
% 0.22/0.44  ipcrm: permission denied for id (816939064)
% 0.22/0.44  ipcrm: permission denied for id (816971833)
% 0.22/0.44  ipcrm: permission denied for id (817004602)
% 0.22/0.44  ipcrm: permission denied for id (813891643)
% 0.22/0.44  ipcrm: permission denied for id (817037372)
% 0.22/0.45  ipcrm: permission denied for id (819200061)
% 0.22/0.45  ipcrm: permission denied for id (820805694)
% 0.22/0.45  ipcrm: permission denied for id (819265599)
% 0.22/0.45  ipcrm: permission denied for id (817168448)
% 0.22/0.45  ipcrm: permission denied for id (814055489)
% 0.22/0.45  ipcrm: permission denied for id (814088258)
% 0.22/0.45  ipcrm: permission denied for id (817201219)
% 0.22/0.45  ipcrm: permission denied for id (819298372)
% 0.22/0.46  ipcrm: permission denied for id (817266757)
% 0.22/0.46  ipcrm: permission denied for id (817299526)
% 0.22/0.46  ipcrm: permission denied for id (814153799)
% 0.22/0.46  ipcrm: permission denied for id (814186568)
% 0.22/0.46  ipcrm: permission denied for id (817332297)
% 0.22/0.46  ipcrm: permission denied for id (819331146)
% 0.22/0.46  ipcrm: permission denied for id (817397835)
% 0.22/0.46  ipcrm: permission denied for id (814252108)
% 0.22/0.47  ipcrm: permission denied for id (820281421)
% 0.22/0.47  ipcrm: permission denied for id (817463374)
% 0.22/0.47  ipcrm: permission denied for id (817496143)
% 0.22/0.47  ipcrm: permission denied for id (814317648)
% 0.22/0.47  ipcrm: permission denied for id (817528913)
% 0.22/0.47  ipcrm: permission denied for id (814350418)
% 0.22/0.47  ipcrm: permission denied for id (820314195)
% 0.22/0.47  ipcrm: permission denied for id (817594452)
% 0.22/0.48  ipcrm: permission denied for id (814448725)
% 0.22/0.48  ipcrm: permission denied for id (814481494)
% 0.22/0.48  ipcrm: permission denied for id (817627223)
% 0.22/0.48  ipcrm: permission denied for id (819429464)
% 0.22/0.48  ipcrm: permission denied for id (814547033)
% 0.22/0.48  ipcrm: permission denied for id (817692762)
% 0.22/0.48  ipcrm: permission denied for id (814579803)
% 0.22/0.48  ipcrm: permission denied for id (820346972)
% 0.22/0.49  ipcrm: permission denied for id (814645341)
% 0.22/0.49  ipcrm: permission denied for id (814678110)
% 0.22/0.49  ipcrm: permission denied for id (814710879)
% 0.22/0.49  ipcrm: permission denied for id (820379744)
% 0.22/0.49  ipcrm: permission denied for id (814743649)
% 0.22/0.49  ipcrm: permission denied for id (817791074)
% 0.22/0.49  ipcrm: permission denied for id (819527779)
% 0.22/0.50  ipcrm: permission denied for id (814841957)
% 0.22/0.50  ipcrm: permission denied for id (814874726)
% 0.22/0.50  ipcrm: permission denied for id (819593319)
% 0.22/0.50  ipcrm: permission denied for id (817922152)
% 0.22/0.50  ipcrm: permission denied for id (814907497)
% 0.22/0.50  ipcrm: permission denied for id (814940268)
% 0.22/0.51  ipcrm: permission denied for id (818020461)
% 0.22/0.51  ipcrm: permission denied for id (818085998)
% 0.22/0.51  ipcrm: permission denied for id (815038575)
% 0.22/0.51  ipcrm: permission denied for id (818118768)
% 0.22/0.51  ipcrm: permission denied for id (818184306)
% 0.22/0.51  ipcrm: permission denied for id (819724403)
% 0.22/0.52  ipcrm: permission denied for id (818249844)
% 0.22/0.52  ipcrm: permission denied for id (820576373)
% 0.22/0.52  ipcrm: permission denied for id (815235190)
% 0.22/0.52  ipcrm: permission denied for id (815267959)
% 0.22/0.52  ipcrm: permission denied for id (820969592)
% 0.22/0.52  ipcrm: permission denied for id (819822713)
% 0.22/0.52  ipcrm: permission denied for id (815333498)
% 0.22/0.52  ipcrm: permission denied for id (818413691)
% 0.22/0.53  ipcrm: permission denied for id (815366268)
% 0.22/0.53  ipcrm: permission denied for id (818446461)
% 0.22/0.53  ipcrm: permission denied for id (821002366)
% 0.22/0.53  ipcrm: permission denied for id (819888255)
% 0.40/0.66  % (8049)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.40/0.67  % (8042)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.40/0.67  % (8060)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.40/0.67  % (8047)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.40/0.68  % (8052)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.40/0.68  % (8064)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.40/0.68  % (8044)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.40/0.69  % (8059)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.40/0.69  % (8063)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.40/0.69  % (8059)Refutation found. Thanks to Tanya!
% 0.40/0.69  % SZS status Theorem for theBenchmark
% 0.40/0.69  % SZS output start Proof for theBenchmark
% 0.40/0.69  fof(f95,plain,(
% 0.40/0.69    $false),
% 0.40/0.69    inference(subsumption_resolution,[],[f94,f74])).
% 0.40/0.69  fof(f74,plain,(
% 0.40/0.69    r2_relset_1(sK1,sK0,sK3,sK3)),
% 0.40/0.69    inference(subsumption_resolution,[],[f49,f45])).
% 0.40/0.69  fof(f45,plain,(
% 0.40/0.69    ~sP4(sK0,sK1)),
% 0.40/0.69    inference(unit_resulting_resolution,[],[f27,f40])).
% 0.40/0.69  fof(f40,plain,(
% 0.40/0.69    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP4(X1,X0)) )),
% 0.40/0.69    inference(general_splitting,[],[f30,f39_D])).
% 0.40/0.69  fof(f39,plain,(
% 0.40/0.69    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP4(X1,X0)) )),
% 0.40/0.69    inference(cnf_transformation,[],[f39_D])).
% 0.40/0.69  fof(f39_D,plain,(
% 0.40/0.69    ( ! [X0,X1] : (( ! [X2] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) <=> ~sP4(X1,X0)) )),
% 0.40/0.69    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 0.40/0.69  fof(f30,plain,(
% 0.40/0.69    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.40/0.69    inference(cnf_transformation,[],[f15])).
% 0.40/0.69  fof(f15,plain,(
% 0.40/0.69    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.40/0.69    inference(flattening,[],[f14])).
% 0.40/0.69  fof(f14,plain,(
% 0.40/0.69    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.40/0.69    inference(ennf_transformation,[],[f8])).
% 0.40/0.69  fof(f8,axiom,(
% 0.40/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.40/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.40/0.69  fof(f27,plain,(
% 0.40/0.69    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.40/0.69    inference(cnf_transformation,[],[f25])).
% 0.40/0.69  fof(f25,plain,(
% 0.40/0.69    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.40/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f24])).
% 0.40/0.69  fof(f24,plain,(
% 0.40/0.69    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.40/0.69    introduced(choice_axiom,[])).
% 0.40/0.69  fof(f13,plain,(
% 0.40/0.69    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.40/0.69    inference(flattening,[],[f12])).
% 0.40/0.69  fof(f12,plain,(
% 0.40/0.69    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.40/0.69    inference(ennf_transformation,[],[f10])).
% 0.40/0.69  fof(f10,negated_conjecture,(
% 0.40/0.69    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.40/0.69    inference(negated_conjecture,[],[f9])).
% 0.40/0.69  fof(f9,conjecture,(
% 0.40/0.69    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.40/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).
% 0.40/0.69  fof(f49,plain,(
% 0.40/0.69    r2_relset_1(sK1,sK0,sK3,sK3) | sP4(sK0,sK1)),
% 0.40/0.69    inference(resolution,[],[f27,f39])).
% 0.40/0.69  fof(f94,plain,(
% 0.40/0.69    ~r2_relset_1(sK1,sK0,sK3,sK3)),
% 0.40/0.69    inference(backward_demodulation,[],[f85,f75])).
% 0.40/0.69  fof(f75,plain,(
% 0.40/0.69    sK3 = k7_relat_1(sK3,sK2)),
% 0.40/0.69    inference(unit_resulting_resolution,[],[f46,f64,f35])).
% 0.40/0.69  fof(f35,plain,(
% 0.40/0.69    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.40/0.69    inference(cnf_transformation,[],[f21])).
% 0.40/0.69  fof(f21,plain,(
% 0.40/0.69    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.40/0.69    inference(flattening,[],[f20])).
% 0.40/0.69  fof(f20,plain,(
% 0.40/0.69    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.40/0.69    inference(ennf_transformation,[],[f5])).
% 0.40/0.69  fof(f5,axiom,(
% 0.40/0.69    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.40/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.40/0.69  fof(f64,plain,(
% 0.40/0.69    r1_tarski(k1_relat_1(sK3),sK2)),
% 0.40/0.69    inference(unit_resulting_resolution,[],[f58,f42])).
% 0.40/0.69  fof(f42,plain,(
% 0.40/0.69    ( ! [X1] : (~r1_tarski(X1,sK1) | r1_tarski(X1,sK2)) )),
% 0.40/0.69    inference(resolution,[],[f28,f32])).
% 0.40/0.69  fof(f32,plain,(
% 0.40/0.69    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.40/0.69    inference(cnf_transformation,[],[f18])).
% 0.40/0.69  fof(f18,plain,(
% 0.40/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.40/0.69    inference(flattening,[],[f17])).
% 0.40/0.69  fof(f17,plain,(
% 0.40/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.40/0.69    inference(ennf_transformation,[],[f1])).
% 0.40/0.69  fof(f1,axiom,(
% 0.40/0.69    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.40/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.40/0.69  fof(f28,plain,(
% 0.40/0.69    r1_tarski(sK1,sK2)),
% 0.40/0.69    inference(cnf_transformation,[],[f25])).
% 0.40/0.69  fof(f58,plain,(
% 0.40/0.69    r1_tarski(k1_relat_1(sK3),sK1)),
% 0.40/0.69    inference(unit_resulting_resolution,[],[f46,f43,f33])).
% 0.40/0.69  fof(f33,plain,(
% 0.40/0.69    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.40/0.69    inference(cnf_transformation,[],[f26])).
% 0.40/0.69  fof(f26,plain,(
% 0.40/0.69    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.40/0.69    inference(nnf_transformation,[],[f19])).
% 0.40/0.69  fof(f19,plain,(
% 0.40/0.69    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.40/0.69    inference(ennf_transformation,[],[f3])).
% 0.40/0.69  fof(f3,axiom,(
% 0.40/0.69    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.40/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.40/0.69  fof(f43,plain,(
% 0.40/0.69    v4_relat_1(sK3,sK1)),
% 0.40/0.69    inference(unit_resulting_resolution,[],[f27,f36])).
% 0.40/0.69  fof(f36,plain,(
% 0.40/0.69    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.40/0.69    inference(cnf_transformation,[],[f22])).
% 0.40/0.69  fof(f22,plain,(
% 0.40/0.69    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.40/0.69    inference(ennf_transformation,[],[f11])).
% 0.40/0.69  fof(f11,plain,(
% 0.40/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.40/0.69    inference(pure_predicate_removal,[],[f6])).
% 0.40/0.69  fof(f6,axiom,(
% 0.40/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.40/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.40/0.69  fof(f46,plain,(
% 0.40/0.69    v1_relat_1(sK3)),
% 0.40/0.69    inference(unit_resulting_resolution,[],[f38,f27,f37])).
% 0.40/0.69  fof(f37,plain,(
% 0.40/0.69    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.40/0.69    inference(cnf_transformation,[],[f23])).
% 0.40/0.69  fof(f23,plain,(
% 0.40/0.69    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.40/0.69    inference(ennf_transformation,[],[f2])).
% 0.40/0.69  fof(f2,axiom,(
% 0.40/0.69    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.40/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.40/0.69  fof(f38,plain,(
% 0.40/0.69    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.40/0.69    inference(cnf_transformation,[],[f4])).
% 0.40/0.69  fof(f4,axiom,(
% 0.40/0.69    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.40/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.40/0.69  fof(f85,plain,(
% 0.40/0.69    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)),
% 0.40/0.69    inference(backward_demodulation,[],[f29,f44])).
% 0.40/0.69  fof(f44,plain,(
% 0.40/0.69    ( ! [X0] : (k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.40/0.69    inference(unit_resulting_resolution,[],[f27,f31])).
% 0.40/0.69  fof(f31,plain,(
% 0.40/0.69    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.40/0.69    inference(cnf_transformation,[],[f16])).
% 0.40/0.69  fof(f16,plain,(
% 0.40/0.69    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.40/0.69    inference(ennf_transformation,[],[f7])).
% 0.40/0.69  fof(f7,axiom,(
% 0.40/0.69    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.40/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.40/0.69  fof(f29,plain,(
% 0.40/0.69    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.40/0.69    inference(cnf_transformation,[],[f25])).
% 0.40/0.69  % SZS output end Proof for theBenchmark
% 0.40/0.69  % (8059)------------------------------
% 0.40/0.69  % (8059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.69  % (8059)Termination reason: Refutation
% 0.40/0.69  
% 0.40/0.69  % (8059)Memory used [KB]: 1663
% 0.40/0.69  % (8059)Time elapsed: 0.116 s
% 0.40/0.69  % (8059)------------------------------
% 0.40/0.69  % (8059)------------------------------
% 0.40/0.69  % (8055)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.40/0.69  % (8045)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.40/0.69  % (7885)Success in time 0.327 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:47 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   52 (  99 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  115 ( 213 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(subsumption_resolution,[],[f97,f43])).

fof(f43,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f27,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

fof(f97,plain,(
    ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f93,f55])).

fof(f55,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(subsumption_resolution,[],[f54,f43])).

fof(f54,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f42,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f42,plain,(
    v5_relat_1(sK3,sK2) ),
    inference(resolution,[],[f27,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f93,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f63,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

fof(f63,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),X0)
      | ~ r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f53,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f53,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) ),
    inference(subsumption_resolution,[],[f52,f50])).

fof(f50,plain,(
    ! [X6] : v1_relat_1(k7_relat_1(sK3,X6)) ),
    inference(resolution,[],[f43,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f52,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f51,f49])).

fof(f49,plain,(
    ! [X5] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X5)),X5) ),
    inference(resolution,[],[f43,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f51,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f44,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f44,plain,(
    ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(backward_demodulation,[],[f28,f40])).

fof(f40,plain,(
    ! [X0] : k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(resolution,[],[f27,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f28,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:10:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (789315584)
% 0.14/0.37  ipcrm: permission denied for id (791478274)
% 0.14/0.37  ipcrm: permission denied for id (791511043)
% 0.14/0.38  ipcrm: permission denied for id (791543812)
% 0.14/0.38  ipcrm: permission denied for id (791576581)
% 0.14/0.38  ipcrm: permission denied for id (789348358)
% 0.14/0.38  ipcrm: permission denied for id (789381127)
% 0.14/0.38  ipcrm: permission denied for id (791609352)
% 0.14/0.38  ipcrm: permission denied for id (791642121)
% 0.14/0.38  ipcrm: permission denied for id (794755082)
% 0.14/0.38  ipcrm: permission denied for id (791707659)
% 0.14/0.39  ipcrm: permission denied for id (789446668)
% 0.14/0.39  ipcrm: permission denied for id (794787853)
% 0.14/0.39  ipcrm: permission denied for id (791773198)
% 0.14/0.39  ipcrm: permission denied for id (794820623)
% 0.14/0.39  ipcrm: permission denied for id (791838736)
% 0.14/0.39  ipcrm: permission denied for id (794853393)
% 0.14/0.39  ipcrm: permission denied for id (789577746)
% 0.14/0.39  ipcrm: permission denied for id (789610515)
% 0.14/0.40  ipcrm: permission denied for id (791904276)
% 0.14/0.40  ipcrm: permission denied for id (791937045)
% 0.14/0.40  ipcrm: permission denied for id (794886166)
% 0.14/0.40  ipcrm: permission denied for id (792002583)
% 0.14/0.40  ipcrm: permission denied for id (796229656)
% 0.14/0.40  ipcrm: permission denied for id (792068121)
% 0.14/0.40  ipcrm: permission denied for id (792100890)
% 0.14/0.40  ipcrm: permission denied for id (794951707)
% 0.14/0.41  ipcrm: permission denied for id (796262428)
% 0.14/0.41  ipcrm: permission denied for id (792199197)
% 0.14/0.41  ipcrm: permission denied for id (796295198)
% 0.14/0.41  ipcrm: permission denied for id (792264735)
% 0.14/0.41  ipcrm: permission denied for id (792297504)
% 0.14/0.41  ipcrm: permission denied for id (789807137)
% 0.14/0.41  ipcrm: permission denied for id (789839906)
% 0.14/0.41  ipcrm: permission denied for id (789872675)
% 0.14/0.42  ipcrm: permission denied for id (795050020)
% 0.14/0.42  ipcrm: permission denied for id (792363045)
% 0.14/0.42  ipcrm: permission denied for id (792395814)
% 0.14/0.42  ipcrm: permission denied for id (792428583)
% 0.14/0.42  ipcrm: permission denied for id (795082792)
% 0.14/0.42  ipcrm: permission denied for id (796327977)
% 0.14/0.42  ipcrm: permission denied for id (796360746)
% 0.14/0.42  ipcrm: permission denied for id (792559659)
% 0.14/0.43  ipcrm: permission denied for id (796393516)
% 0.14/0.43  ipcrm: permission denied for id (792625197)
% 0.14/0.43  ipcrm: permission denied for id (795213870)
% 0.14/0.43  ipcrm: permission denied for id (795246639)
% 0.14/0.43  ipcrm: permission denied for id (792756272)
% 0.21/0.43  ipcrm: permission denied for id (792789041)
% 0.21/0.43  ipcrm: permission denied for id (792821810)
% 0.21/0.43  ipcrm: permission denied for id (792854579)
% 0.21/0.44  ipcrm: permission denied for id (795279412)
% 0.21/0.44  ipcrm: permission denied for id (795312181)
% 0.21/0.44  ipcrm: permission denied for id (790036535)
% 0.21/0.44  ipcrm: permission denied for id (792985656)
% 0.21/0.44  ipcrm: permission denied for id (790102073)
% 0.21/0.44  ipcrm: permission denied for id (793018426)
% 0.21/0.44  ipcrm: permission denied for id (790134843)
% 0.21/0.44  ipcrm: permission denied for id (795377724)
% 0.21/0.45  ipcrm: permission denied for id (793083965)
% 0.21/0.45  ipcrm: permission denied for id (793116734)
% 0.21/0.45  ipcrm: permission denied for id (793149503)
% 0.21/0.45  ipcrm: permission denied for id (795410496)
% 0.21/0.45  ipcrm: permission denied for id (793215041)
% 0.21/0.45  ipcrm: permission denied for id (793247810)
% 0.21/0.45  ipcrm: permission denied for id (796459075)
% 0.21/0.45  ipcrm: permission denied for id (795476036)
% 0.21/0.46  ipcrm: permission denied for id (793346117)
% 0.21/0.46  ipcrm: permission denied for id (793378886)
% 0.21/0.46  ipcrm: permission denied for id (795508807)
% 0.21/0.46  ipcrm: permission denied for id (793444424)
% 0.21/0.46  ipcrm: permission denied for id (793477193)
% 0.21/0.46  ipcrm: permission denied for id (790298698)
% 0.21/0.46  ipcrm: permission denied for id (796491851)
% 0.21/0.46  ipcrm: permission denied for id (795574348)
% 0.21/0.47  ipcrm: permission denied for id (790364237)
% 0.21/0.47  ipcrm: permission denied for id (795607118)
% 0.21/0.47  ipcrm: permission denied for id (793641039)
% 0.21/0.47  ipcrm: permission denied for id (795639888)
% 0.21/0.47  ipcrm: permission denied for id (793706577)
% 0.21/0.47  ipcrm: permission denied for id (790495314)
% 0.21/0.47  ipcrm: permission denied for id (790528083)
% 0.21/0.47  ipcrm: permission denied for id (790560852)
% 0.21/0.48  ipcrm: permission denied for id (790626389)
% 0.21/0.48  ipcrm: permission denied for id (793739350)
% 0.21/0.48  ipcrm: permission denied for id (795672663)
% 0.21/0.48  ipcrm: permission denied for id (793804888)
% 0.21/0.48  ipcrm: permission denied for id (790691929)
% 0.21/0.48  ipcrm: permission denied for id (795705434)
% 0.21/0.48  ipcrm: permission denied for id (790757467)
% 0.21/0.48  ipcrm: permission denied for id (793870428)
% 0.21/0.49  ipcrm: permission denied for id (796524637)
% 0.21/0.49  ipcrm: permission denied for id (790888542)
% 0.21/0.49  ipcrm: permission denied for id (790921311)
% 0.21/0.49  ipcrm: permission denied for id (793935968)
% 0.21/0.49  ipcrm: permission denied for id (796557409)
% 0.21/0.49  ipcrm: permission denied for id (790986851)
% 0.21/0.49  ipcrm: permission denied for id (791019620)
% 0.21/0.50  ipcrm: permission denied for id (791052389)
% 0.21/0.50  ipcrm: permission denied for id (796622950)
% 0.21/0.50  ipcrm: permission denied for id (791085159)
% 0.21/0.50  ipcrm: permission denied for id (794067048)
% 0.21/0.50  ipcrm: permission denied for id (796655721)
% 0.21/0.50  ipcrm: permission denied for id (795902058)
% 0.21/0.50  ipcrm: permission denied for id (791150699)
% 0.21/0.50  ipcrm: permission denied for id (794165356)
% 0.21/0.51  ipcrm: permission denied for id (791183469)
% 0.21/0.51  ipcrm: permission denied for id (794198126)
% 0.21/0.51  ipcrm: permission denied for id (795934831)
% 0.21/0.51  ipcrm: permission denied for id (796885104)
% 0.21/0.51  ipcrm: permission denied for id (791281777)
% 0.21/0.51  ipcrm: permission denied for id (794296434)
% 0.21/0.51  ipcrm: permission denied for id (796000371)
% 0.21/0.51  ipcrm: permission denied for id (796033140)
% 0.21/0.52  ipcrm: permission denied for id (794394741)
% 0.21/0.52  ipcrm: permission denied for id (796065910)
% 0.21/0.52  ipcrm: permission denied for id (791347319)
% 0.21/0.52  ipcrm: permission denied for id (794460280)
% 0.21/0.52  ipcrm: permission denied for id (794493049)
% 0.21/0.52  ipcrm: permission denied for id (794558587)
% 0.21/0.52  ipcrm: permission denied for id (796131452)
% 0.21/0.53  ipcrm: permission denied for id (794624125)
% 0.21/0.53  ipcrm: permission denied for id (794656894)
% 0.21/0.53  ipcrm: permission denied for id (796950655)
% 0.75/0.63  % (13784)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.75/0.64  % (13791)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.75/0.64  % (13791)Refutation found. Thanks to Tanya!
% 0.75/0.64  % SZS status Theorem for theBenchmark
% 0.75/0.64  % SZS output start Proof for theBenchmark
% 0.75/0.64  fof(f98,plain,(
% 0.75/0.64    $false),
% 0.75/0.64    inference(subsumption_resolution,[],[f97,f43])).
% 0.75/0.64  fof(f43,plain,(
% 0.75/0.64    v1_relat_1(sK3)),
% 0.75/0.64    inference(resolution,[],[f27,f35])).
% 0.75/0.64  fof(f35,plain,(
% 0.75/0.64    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.75/0.64    inference(cnf_transformation,[],[f19])).
% 0.75/0.64  fof(f19,plain,(
% 0.75/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.75/0.64    inference(ennf_transformation,[],[f6])).
% 0.75/0.64  fof(f6,axiom,(
% 0.75/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.75/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.75/0.64  fof(f27,plain,(
% 0.75/0.64    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.75/0.64    inference(cnf_transformation,[],[f25])).
% 0.75/0.64  fof(f25,plain,(
% 0.75/0.64    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.75/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f24])).
% 0.75/0.64  fof(f24,plain,(
% 0.75/0.64    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 0.75/0.64    introduced(choice_axiom,[])).
% 0.75/0.64  fof(f12,plain,(
% 0.75/0.64    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.75/0.64    inference(ennf_transformation,[],[f11])).
% 0.75/0.64  fof(f11,negated_conjecture,(
% 0.75/0.64    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.75/0.64    inference(negated_conjecture,[],[f10])).
% 0.75/0.64  fof(f10,conjecture,(
% 0.75/0.64    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.75/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).
% 0.75/0.64  fof(f97,plain,(
% 0.75/0.64    ~v1_relat_1(sK3)),
% 0.75/0.64    inference(subsumption_resolution,[],[f93,f55])).
% 0.75/0.64  fof(f55,plain,(
% 0.75/0.64    r1_tarski(k2_relat_1(sK3),sK2)),
% 0.75/0.64    inference(subsumption_resolution,[],[f54,f43])).
% 0.75/0.64  fof(f54,plain,(
% 0.75/0.64    r1_tarski(k2_relat_1(sK3),sK2) | ~v1_relat_1(sK3)),
% 0.75/0.64    inference(resolution,[],[f42,f32])).
% 0.75/0.64  fof(f32,plain,(
% 0.75/0.64    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.75/0.64    inference(cnf_transformation,[],[f26])).
% 0.75/0.64  fof(f26,plain,(
% 0.75/0.64    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.75/0.64    inference(nnf_transformation,[],[f16])).
% 0.75/0.64  fof(f16,plain,(
% 0.75/0.64    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.75/0.64    inference(ennf_transformation,[],[f2])).
% 0.75/0.64  fof(f2,axiom,(
% 0.75/0.64    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.75/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.75/0.64  fof(f42,plain,(
% 0.75/0.64    v5_relat_1(sK3,sK2)),
% 0.75/0.64    inference(resolution,[],[f27,f37])).
% 0.75/0.64  fof(f37,plain,(
% 0.75/0.64    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.75/0.64    inference(cnf_transformation,[],[f20])).
% 0.75/0.64  fof(f20,plain,(
% 0.75/0.64    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.75/0.64    inference(ennf_transformation,[],[f7])).
% 0.75/0.64  fof(f7,axiom,(
% 0.75/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.75/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.75/0.64  fof(f93,plain,(
% 0.75/0.64    ~r1_tarski(k2_relat_1(sK3),sK2) | ~v1_relat_1(sK3)),
% 0.75/0.64    inference(resolution,[],[f63,f31])).
% 0.75/0.64  fof(f31,plain,(
% 0.75/0.64    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.75/0.64    inference(cnf_transformation,[],[f15])).
% 0.75/0.64  fof(f15,plain,(
% 0.75/0.64    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.75/0.64    inference(ennf_transformation,[],[f5])).
% 0.75/0.64  fof(f5,axiom,(
% 0.75/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 0.75/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).
% 0.75/0.64  fof(f63,plain,(
% 0.75/0.64    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),X0) | ~r1_tarski(X0,sK2)) )),
% 0.75/0.64    inference(resolution,[],[f53,f38])).
% 0.75/0.64  fof(f38,plain,(
% 0.75/0.64    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.75/0.64    inference(cnf_transformation,[],[f22])).
% 0.75/0.64  fof(f22,plain,(
% 0.75/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.75/0.64    inference(flattening,[],[f21])).
% 0.75/0.64  fof(f21,plain,(
% 0.75/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.75/0.64    inference(ennf_transformation,[],[f1])).
% 0.75/0.64  fof(f1,axiom,(
% 0.75/0.64    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.75/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.75/0.64  fof(f53,plain,(
% 0.75/0.64    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)),
% 0.75/0.64    inference(subsumption_resolution,[],[f52,f50])).
% 0.75/0.64  fof(f50,plain,(
% 0.75/0.64    ( ! [X6] : (v1_relat_1(k7_relat_1(sK3,X6))) )),
% 0.75/0.64    inference(resolution,[],[f43,f29])).
% 0.75/0.64  fof(f29,plain,(
% 0.75/0.64    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.75/0.64    inference(cnf_transformation,[],[f13])).
% 0.75/0.64  fof(f13,plain,(
% 0.75/0.64    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.75/0.64    inference(ennf_transformation,[],[f3])).
% 0.75/0.64  fof(f3,axiom,(
% 0.75/0.64    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.75/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.75/0.64  fof(f52,plain,(
% 0.75/0.64    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) | ~v1_relat_1(k7_relat_1(sK3,sK1))),
% 0.75/0.64    inference(subsumption_resolution,[],[f51,f49])).
% 0.75/0.64  fof(f49,plain,(
% 0.75/0.64    ( ! [X5] : (r1_tarski(k1_relat_1(k7_relat_1(sK3,X5)),X5)) )),
% 0.75/0.64    inference(resolution,[],[f43,f30])).
% 0.75/0.64  fof(f30,plain,(
% 0.75/0.64    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.75/0.64    inference(cnf_transformation,[],[f14])).
% 0.75/0.64  fof(f14,plain,(
% 0.75/0.64    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.75/0.64    inference(ennf_transformation,[],[f4])).
% 0.75/0.64  fof(f4,axiom,(
% 0.75/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.75/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.75/0.64  fof(f51,plain,(
% 0.75/0.64    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | ~v1_relat_1(k7_relat_1(sK3,sK1))),
% 0.75/0.64    inference(resolution,[],[f44,f34])).
% 0.75/0.64  fof(f34,plain,(
% 0.75/0.64    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.75/0.64    inference(cnf_transformation,[],[f18])).
% 0.75/0.64  fof(f18,plain,(
% 0.75/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.75/0.64    inference(flattening,[],[f17])).
% 0.75/0.64  fof(f17,plain,(
% 0.75/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.75/0.64    inference(ennf_transformation,[],[f9])).
% 0.75/0.64  fof(f9,axiom,(
% 0.75/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.75/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.75/0.64  fof(f44,plain,(
% 0.75/0.64    ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.75/0.64    inference(backward_demodulation,[],[f28,f40])).
% 0.75/0.64  fof(f40,plain,(
% 0.75/0.64    ( ! [X0] : (k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.75/0.64    inference(resolution,[],[f27,f39])).
% 0.75/0.64  fof(f39,plain,(
% 0.75/0.64    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.75/0.64    inference(cnf_transformation,[],[f23])).
% 0.75/0.64  fof(f23,plain,(
% 0.75/0.64    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.75/0.64    inference(ennf_transformation,[],[f8])).
% 0.75/0.64  fof(f8,axiom,(
% 0.75/0.64    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.75/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.75/0.64  fof(f28,plain,(
% 0.75/0.64    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.75/0.64    inference(cnf_transformation,[],[f25])).
% 0.75/0.64  % SZS output end Proof for theBenchmark
% 0.75/0.64  % (13791)------------------------------
% 0.75/0.64  % (13791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.75/0.64  % (13791)Termination reason: Refutation
% 0.75/0.64  
% 0.75/0.64  % (13791)Memory used [KB]: 1663
% 0.75/0.64  % (13791)Time elapsed: 0.059 s
% 0.75/0.64  % (13791)------------------------------
% 0.75/0.64  % (13791)------------------------------
% 0.75/0.64  % (13624)Success in time 0.276 s
%------------------------------------------------------------------------------

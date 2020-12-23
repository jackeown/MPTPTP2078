%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0830+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:50 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   42 (  59 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :   22
%              Number of atoms          :   72 ( 110 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4214,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4194,f3565])).

fof(f3565,plain,(
    v1_relat_1(sK91) ),
    inference(resolution,[],[f2354,f2468])).

fof(f2468,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1314])).

fof(f1314,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f2354,plain,(
    m1_subset_1(sK91,k1_zfmisc_1(k2_zfmisc_1(sK88,sK90))) ),
    inference(cnf_transformation,[],[f1915])).

fof(f1915,plain,
    ( ~ m1_subset_1(k5_relset_1(sK88,sK90,sK91,sK89),k1_zfmisc_1(k2_zfmisc_1(sK89,sK90)))
    & m1_subset_1(sK91,k1_zfmisc_1(k2_zfmisc_1(sK88,sK90))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK88,sK89,sK90,sK91])],[f1253,f1914])).

fof(f1914,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(k5_relset_1(sK88,sK90,sK91,sK89),k1_zfmisc_1(k2_zfmisc_1(sK89,sK90)))
      & m1_subset_1(sK91,k1_zfmisc_1(k2_zfmisc_1(sK88,sK90))) ) ),
    introduced(choice_axiom,[])).

fof(f1253,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f1242])).

fof(f1242,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f1241])).

fof(f1241,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

fof(f4194,plain,(
    ~ v1_relat_1(sK91) ),
    inference(resolution,[],[f4191,f2562])).

fof(f2562,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1395])).

fof(f1395,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f876])).

fof(f876,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f4191,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1(sK91,sK89)),sK89) ),
    inference(subsumption_resolution,[],[f4186,f2354])).

fof(f4186,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK91,sK89)),sK89)
    | ~ m1_subset_1(sK91,k1_zfmisc_1(k2_zfmisc_1(sK88,sK90))) ),
    inference(superposition,[],[f4182,f2357])).

fof(f2357,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1255])).

fof(f1255,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1224])).

fof(f1224,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f4182,plain,(
    ~ r1_tarski(k1_relat_1(k5_relset_1(sK88,sK90,sK91,sK89)),sK89) ),
    inference(global_subsumption,[],[f4181])).

fof(f4181,plain,(
    ~ r1_tarski(k1_relat_1(k5_relset_1(sK88,sK90,sK91,sK89)),sK89) ),
    inference(global_subsumption,[],[f4180])).

fof(f4180,plain,(
    ~ r1_tarski(k1_relat_1(k5_relset_1(sK88,sK90,sK91,sK89)),sK89) ),
    inference(global_subsumption,[],[f4179])).

fof(f4179,plain,(
    ~ r1_tarski(k1_relat_1(k5_relset_1(sK88,sK90,sK91,sK89)),sK89) ),
    inference(global_subsumption,[],[f4177])).

fof(f4177,plain,(
    ~ r1_tarski(k1_relat_1(k5_relset_1(sK88,sK90,sK91,sK89)),sK89) ),
    inference(global_subsumption,[],[f4176])).

fof(f4176,plain,(
    ~ r1_tarski(k1_relat_1(k5_relset_1(sK88,sK90,sK91,sK89)),sK89) ),
    inference(global_subsumption,[],[f4174])).

fof(f4174,plain,(
    ~ r1_tarski(k1_relat_1(k5_relset_1(sK88,sK90,sK91,sK89)),sK89) ),
    inference(global_subsumption,[],[f4173])).

fof(f4173,plain,(
    ~ r1_tarski(k1_relat_1(k5_relset_1(sK88,sK90,sK91,sK89)),sK89) ),
    inference(global_subsumption,[],[f4172])).

fof(f4172,plain,(
    ~ r1_tarski(k1_relat_1(k5_relset_1(sK88,sK90,sK91,sK89)),sK89) ),
    inference(global_subsumption,[],[f4171])).

fof(f4171,plain,(
    ~ r1_tarski(k1_relat_1(k5_relset_1(sK88,sK90,sK91,sK89)),sK89) ),
    inference(global_subsumption,[],[f4170])).

fof(f4170,plain,(
    ~ r1_tarski(k1_relat_1(k5_relset_1(sK88,sK90,sK91,sK89)),sK89) ),
    inference(global_subsumption,[],[f4169])).

fof(f4169,plain,(
    ~ r1_tarski(k1_relat_1(k5_relset_1(sK88,sK90,sK91,sK89)),sK89) ),
    inference(subsumption_resolution,[],[f4151,f2354])).

fof(f4151,plain,
    ( ~ r1_tarski(k1_relat_1(k5_relset_1(sK88,sK90,sK91,sK89)),sK89)
    | ~ m1_subset_1(sK91,k1_zfmisc_1(k2_zfmisc_1(sK88,sK90))) ),
    inference(resolution,[],[f3586,f2356])).

fof(f2356,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1254])).

fof(f1254,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1217])).

fof(f1217,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relset_1)).

fof(f3586,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k5_relset_1(sK88,sK90,sK91,sK89),k1_zfmisc_1(k2_zfmisc_1(X2,sK90)))
      | ~ r1_tarski(k1_relat_1(k5_relset_1(sK88,sK90,sK91,sK89)),sK89) ) ),
    inference(resolution,[],[f2355,f2447])).

fof(f2447,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f1306])).

fof(f1306,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f1305])).

fof(f1305,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f1228])).

fof(f1228,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f2355,plain,(
    ~ m1_subset_1(k5_relset_1(sK88,sK90,sK91,sK89),k1_zfmisc_1(k2_zfmisc_1(sK89,sK90))) ),
    inference(cnf_transformation,[],[f1915])).
%------------------------------------------------------------------------------

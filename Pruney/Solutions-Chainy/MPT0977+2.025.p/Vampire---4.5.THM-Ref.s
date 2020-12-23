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
% DateTime   : Thu Dec  3 13:01:19 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 181 expanded)
%              Number of leaves         :   17 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  188 ( 458 expanded)
%              Number of equality atoms :   39 (  55 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f599,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f533,f598])).

fof(f598,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f597])).

fof(f597,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f596,f156])).

fof(f156,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f77,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
        | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f596,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl3_2 ),
    inference(forward_demodulation,[],[f595,f200])).

fof(f200,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    inference(subsumption_resolution,[],[f198,f93])).

fof(f93,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f90,f52])).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f90,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f51,f42])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f198,plain,
    ( sK2 = k5_relat_1(sK2,k6_partfun1(sK1))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f188,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f54,f44])).

fof(f44,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

% (24167)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f54,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f188,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f185,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

% (24166)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f185,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f183,f42])).

fof(f183,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f62,f169])).

fof(f169,plain,(
    k2_relat_1(sK2) = k2_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f61,f42])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f595,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2)
    | spl3_2 ),
    inference(backward_demodulation,[],[f85,f429])).

fof(f429,plain,(
    ! [X14] : k4_relset_1(sK0,sK1,X14,X14,sK2,k6_partfun1(X14)) = k5_relat_1(sK2,k6_partfun1(X14)) ),
    inference(resolution,[],[f215,f42])).

fof(f215,plain,(
    ! [X21,X19,X20,X18] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | k4_relset_1(X18,X19,X20,X20,X21,k6_partfun1(X20)) = k5_relat_1(X21,k6_partfun1(X20)) ) ),
    inference(resolution,[],[f67,f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f85,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_2
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f533,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f532])).

fof(f532,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f531,f156])).

fof(f531,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl3_1 ),
    inference(forward_demodulation,[],[f530,f134])).

fof(f134,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f129,f93])).

fof(f129,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f58,f111])).

fof(f111,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f63,f42])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f530,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2)
    | spl3_1 ),
    inference(backward_demodulation,[],[f81,f326])).

fof(f326,plain,(
    ! [X9] : k4_relset_1(X9,X9,sK0,sK1,k6_partfun1(X9),sK2) = k7_relat_1(sK2,X9) ),
    inference(forward_demodulation,[],[f324,f137])).

fof(f137,plain,(
    ! [X5] : k7_relat_1(sK2,X5) = k5_relat_1(k6_partfun1(X5),sK2) ),
    inference(resolution,[],[f74,f93])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(definition_unfolding,[],[f53,f44])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f324,plain,(
    ! [X9] : k4_relset_1(X9,X9,sK0,sK1,k6_partfun1(X9),sK2) = k5_relat_1(k6_partfun1(X9),sK2) ),
    inference(resolution,[],[f216,f68])).

fof(f216,plain,(
    ! [X24,X23,X22] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k4_relset_1(X22,X23,sK0,sK1,X24,sK2) = k5_relat_1(X24,sK2) ) ),
    inference(resolution,[],[f67,f42])).

fof(f81,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_1
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f86,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f43,f83,f79])).

fof(f43,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f38])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 18:48:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (24145)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (24144)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (24153)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (24161)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (24143)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (24149)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.29/0.53  % (24142)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.29/0.53  % (24159)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.29/0.53  % (24145)Refutation found. Thanks to Tanya!
% 1.29/0.53  % SZS status Theorem for theBenchmark
% 1.29/0.53  % (24162)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.29/0.53  % (24141)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.29/0.54  % (24154)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.29/0.54  % (24150)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.29/0.54  % SZS output start Proof for theBenchmark
% 1.29/0.54  fof(f599,plain,(
% 1.29/0.54    $false),
% 1.29/0.54    inference(avatar_sat_refutation,[],[f86,f533,f598])).
% 1.29/0.54  fof(f598,plain,(
% 1.29/0.54    spl3_2),
% 1.29/0.54    inference(avatar_contradiction_clause,[],[f597])).
% 1.29/0.54  fof(f597,plain,(
% 1.29/0.54    $false | spl3_2),
% 1.29/0.54    inference(subsumption_resolution,[],[f596,f156])).
% 1.29/0.54  fof(f156,plain,(
% 1.29/0.54    r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.29/0.54    inference(resolution,[],[f77,f42])).
% 1.29/0.54  fof(f42,plain,(
% 1.29/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.29/0.54    inference(cnf_transformation,[],[f38])).
% 1.29/0.54  fof(f38,plain,(
% 1.29/0.54    (~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.29/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f37])).
% 1.29/0.54  fof(f37,plain,(
% 1.29/0.54    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 1.29/0.54    introduced(choice_axiom,[])).
% 1.29/0.54  fof(f20,plain,(
% 1.29/0.54    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.54    inference(ennf_transformation,[],[f19])).
% 1.29/0.54  fof(f19,negated_conjecture,(
% 1.29/0.54    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 1.29/0.54    inference(negated_conjecture,[],[f18])).
% 1.29/0.54  fof(f18,conjecture,(
% 1.29/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).
% 1.29/0.54  fof(f77,plain,(
% 1.29/0.54    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.29/0.54    inference(duplicate_literal_removal,[],[f76])).
% 1.29/0.54  fof(f76,plain,(
% 1.29/0.54    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.29/0.54    inference(equality_resolution,[],[f66])).
% 1.29/0.54  fof(f66,plain,(
% 1.29/0.54    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.29/0.54    inference(cnf_transformation,[],[f41])).
% 1.29/0.54  fof(f41,plain,(
% 1.29/0.54    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.54    inference(nnf_transformation,[],[f34])).
% 1.29/0.54  fof(f34,plain,(
% 1.29/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.54    inference(flattening,[],[f33])).
% 1.29/0.54  fof(f33,plain,(
% 1.29/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.29/0.54    inference(ennf_transformation,[],[f15])).
% 1.29/0.54  fof(f15,axiom,(
% 1.29/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.29/0.54  fof(f596,plain,(
% 1.29/0.54    ~r2_relset_1(sK0,sK1,sK2,sK2) | spl3_2),
% 1.29/0.54    inference(forward_demodulation,[],[f595,f200])).
% 1.29/0.54  fof(f200,plain,(
% 1.29/0.54    sK2 = k5_relat_1(sK2,k6_partfun1(sK1))),
% 1.29/0.54    inference(subsumption_resolution,[],[f198,f93])).
% 1.29/0.54  fof(f93,plain,(
% 1.29/0.54    v1_relat_1(sK2)),
% 1.29/0.54    inference(subsumption_resolution,[],[f90,f52])).
% 1.29/0.54  fof(f52,plain,(
% 1.29/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.29/0.54    inference(cnf_transformation,[],[f4])).
% 1.29/0.54  fof(f4,axiom,(
% 1.29/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.29/0.54  fof(f90,plain,(
% 1.29/0.54    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.29/0.54    inference(resolution,[],[f51,f42])).
% 1.29/0.54  fof(f51,plain,(
% 1.29/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f21])).
% 1.29/0.54  fof(f21,plain,(
% 1.29/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.29/0.54    inference(ennf_transformation,[],[f2])).
% 1.29/0.54  fof(f2,axiom,(
% 1.29/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.29/0.54  fof(f198,plain,(
% 1.29/0.54    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) | ~v1_relat_1(sK2)),
% 1.29/0.54    inference(resolution,[],[f188,f75])).
% 1.29/0.54  fof(f75,plain,(
% 1.29/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f54,f44])).
% 1.29/0.54  fof(f44,plain,(
% 1.29/0.54    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f17])).
% 1.29/0.54  fof(f17,axiom,(
% 1.29/0.54    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.29/0.54  % (24167)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.29/0.54  fof(f54,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f24])).
% 1.29/0.54  fof(f24,plain,(
% 1.29/0.54    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.29/0.54    inference(flattening,[],[f23])).
% 1.29/0.54  fof(f23,plain,(
% 1.29/0.54    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.29/0.54    inference(ennf_transformation,[],[f8])).
% 1.29/0.54  fof(f8,axiom,(
% 1.29/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 1.29/0.54  fof(f188,plain,(
% 1.29/0.54    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.29/0.54    inference(resolution,[],[f185,f59])).
% 1.29/0.54  fof(f59,plain,(
% 1.29/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f40])).
% 1.29/0.54  % (24166)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.29/0.54  fof(f40,plain,(
% 1.29/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.29/0.54    inference(nnf_transformation,[],[f1])).
% 1.29/0.54  fof(f1,axiom,(
% 1.29/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.29/0.54  fof(f185,plain,(
% 1.29/0.54    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 1.29/0.54    inference(subsumption_resolution,[],[f183,f42])).
% 1.29/0.54  fof(f183,plain,(
% 1.29/0.54    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.29/0.54    inference(superposition,[],[f62,f169])).
% 1.29/0.54  fof(f169,plain,(
% 1.29/0.54    k2_relat_1(sK2) = k2_relset_1(sK0,sK1,sK2)),
% 1.29/0.54    inference(resolution,[],[f61,f42])).
% 1.29/0.54  fof(f61,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f30])).
% 1.29/0.54  fof(f30,plain,(
% 1.29/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.54    inference(ennf_transformation,[],[f13])).
% 1.29/0.54  fof(f13,axiom,(
% 1.29/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.29/0.54  fof(f62,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.29/0.54    inference(cnf_transformation,[],[f31])).
% 1.29/0.54  fof(f31,plain,(
% 1.29/0.54    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.54    inference(ennf_transformation,[],[f12])).
% 1.29/0.54  fof(f12,axiom,(
% 1.29/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.29/0.54  fof(f595,plain,(
% 1.29/0.54    ~r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2) | spl3_2),
% 1.29/0.54    inference(backward_demodulation,[],[f85,f429])).
% 1.29/0.54  fof(f429,plain,(
% 1.29/0.54    ( ! [X14] : (k4_relset_1(sK0,sK1,X14,X14,sK2,k6_partfun1(X14)) = k5_relat_1(sK2,k6_partfun1(X14))) )),
% 1.29/0.54    inference(resolution,[],[f215,f42])).
% 1.29/0.54  fof(f215,plain,(
% 1.29/0.54    ( ! [X21,X19,X20,X18] : (~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) | k4_relset_1(X18,X19,X20,X20,X21,k6_partfun1(X20)) = k5_relat_1(X21,k6_partfun1(X20))) )),
% 1.29/0.54    inference(resolution,[],[f67,f68])).
% 1.29/0.54  fof(f68,plain,(
% 1.29/0.54    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.29/0.54    inference(definition_unfolding,[],[f45,f44])).
% 1.29/0.54  fof(f45,plain,(
% 1.29/0.54    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.29/0.54    inference(cnf_transformation,[],[f16])).
% 1.29/0.54  fof(f16,axiom,(
% 1.29/0.54    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.29/0.54  fof(f67,plain,(
% 1.29/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.29/0.54    inference(cnf_transformation,[],[f36])).
% 1.29/0.54  fof(f36,plain,(
% 1.29/0.54    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.54    inference(flattening,[],[f35])).
% 1.29/0.54  fof(f35,plain,(
% 1.29/0.54    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.29/0.54    inference(ennf_transformation,[],[f14])).
% 1.29/0.54  fof(f14,axiom,(
% 1.29/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 1.29/0.54  fof(f85,plain,(
% 1.29/0.54    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | spl3_2),
% 1.29/0.54    inference(avatar_component_clause,[],[f83])).
% 1.29/0.54  fof(f83,plain,(
% 1.29/0.54    spl3_2 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)),
% 1.29/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.29/0.54  fof(f533,plain,(
% 1.29/0.54    spl3_1),
% 1.29/0.54    inference(avatar_contradiction_clause,[],[f532])).
% 1.29/0.54  fof(f532,plain,(
% 1.29/0.54    $false | spl3_1),
% 1.29/0.54    inference(subsumption_resolution,[],[f531,f156])).
% 1.29/0.54  fof(f531,plain,(
% 1.29/0.54    ~r2_relset_1(sK0,sK1,sK2,sK2) | spl3_1),
% 1.29/0.54    inference(forward_demodulation,[],[f530,f134])).
% 1.29/0.54  fof(f134,plain,(
% 1.29/0.54    sK2 = k7_relat_1(sK2,sK0)),
% 1.29/0.54    inference(subsumption_resolution,[],[f129,f93])).
% 1.29/0.54  fof(f129,plain,(
% 1.29/0.54    sK2 = k7_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 1.29/0.54    inference(resolution,[],[f58,f111])).
% 1.29/0.54  fof(f111,plain,(
% 1.29/0.54    v4_relat_1(sK2,sK0)),
% 1.29/0.54    inference(resolution,[],[f63,f42])).
% 1.29/0.54  fof(f63,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f32])).
% 1.29/0.54  fof(f32,plain,(
% 1.29/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.54    inference(ennf_transformation,[],[f11])).
% 1.29/0.54  fof(f11,axiom,(
% 1.29/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.29/0.54  fof(f58,plain,(
% 1.29/0.54    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f29])).
% 1.29/0.54  fof(f29,plain,(
% 1.29/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.29/0.54    inference(flattening,[],[f28])).
% 1.29/0.54  fof(f28,plain,(
% 1.29/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.29/0.54    inference(ennf_transformation,[],[f5])).
% 1.29/0.54  fof(f5,axiom,(
% 1.29/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.29/0.54  fof(f530,plain,(
% 1.29/0.54    ~r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2) | spl3_1),
% 1.29/0.54    inference(backward_demodulation,[],[f81,f326])).
% 1.29/0.54  fof(f326,plain,(
% 1.29/0.54    ( ! [X9] : (k4_relset_1(X9,X9,sK0,sK1,k6_partfun1(X9),sK2) = k7_relat_1(sK2,X9)) )),
% 1.29/0.54    inference(forward_demodulation,[],[f324,f137])).
% 1.29/0.54  fof(f137,plain,(
% 1.29/0.54    ( ! [X5] : (k7_relat_1(sK2,X5) = k5_relat_1(k6_partfun1(X5),sK2)) )),
% 1.29/0.54    inference(resolution,[],[f74,f93])).
% 1.29/0.54  fof(f74,plain,(
% 1.29/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f53,f44])).
% 1.29/0.54  fof(f53,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f22])).
% 1.29/0.54  fof(f22,plain,(
% 1.29/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.29/0.54    inference(ennf_transformation,[],[f9])).
% 1.29/0.54  fof(f9,axiom,(
% 1.29/0.54    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.29/0.54  fof(f324,plain,(
% 1.29/0.54    ( ! [X9] : (k4_relset_1(X9,X9,sK0,sK1,k6_partfun1(X9),sK2) = k5_relat_1(k6_partfun1(X9),sK2)) )),
% 1.29/0.54    inference(resolution,[],[f216,f68])).
% 1.29/0.54  fof(f216,plain,(
% 1.29/0.54    ( ! [X24,X23,X22] : (~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | k4_relset_1(X22,X23,sK0,sK1,X24,sK2) = k5_relat_1(X24,sK2)) )),
% 1.29/0.54    inference(resolution,[],[f67,f42])).
% 1.29/0.54  fof(f81,plain,(
% 1.29/0.54    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) | spl3_1),
% 1.29/0.54    inference(avatar_component_clause,[],[f79])).
% 1.29/0.54  fof(f79,plain,(
% 1.29/0.54    spl3_1 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 1.29/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.29/0.54  fof(f86,plain,(
% 1.29/0.54    ~spl3_1 | ~spl3_2),
% 1.29/0.54    inference(avatar_split_clause,[],[f43,f83,f79])).
% 1.29/0.54  fof(f43,plain,(
% 1.29/0.54    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 1.29/0.54    inference(cnf_transformation,[],[f38])).
% 1.29/0.54  % SZS output end Proof for theBenchmark
% 1.29/0.54  % (24145)------------------------------
% 1.29/0.54  % (24145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (24145)Termination reason: Refutation
% 1.29/0.54  
% 1.29/0.54  % (24145)Memory used [KB]: 11129
% 1.29/0.54  % (24145)Time elapsed: 0.121 s
% 1.29/0.54  % (24145)------------------------------
% 1.29/0.54  % (24145)------------------------------
% 1.29/0.54  % (24146)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.29/0.54  % (24138)Success in time 0.18 s
%------------------------------------------------------------------------------

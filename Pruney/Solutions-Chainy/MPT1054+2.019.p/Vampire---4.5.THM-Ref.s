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
% DateTime   : Thu Dec  3 13:07:08 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 114 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  190 ( 251 expanded)
%              Number of equality atoms :   43 (  69 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f81,f120,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v4_relat_1(k6_partfun1(X0),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f79,f58])).

fof(f58,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f40,f38])).

fof(f38,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( v4_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(k6_partfun1(X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f46,f57])).

fof(f57,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(definition_unfolding,[],[f41,f38])).

fof(f41,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_relat_1(X2,X0)
      | v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

fof(f120,plain,(
    ~ v4_relat_1(k6_partfun1(sK2),sK1) ),
    inference(trivial_inequality_removal,[],[f118])).

fof(f118,plain,
    ( sK2 != sK2
    | ~ v4_relat_1(k6_partfun1(sK2),sK1) ),
    inference(superposition,[],[f90,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_partfun1(X1),X0) = X0
      | ~ v4_relat_1(k6_partfun1(X0),X1) ) ),
    inference(forward_demodulation,[],[f105,f60])).

fof(f60,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f38])).

fof(f42,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f105,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_partfun1(X0)) = k10_relat_1(k6_partfun1(X1),X0)
      | ~ v4_relat_1(k6_partfun1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f103,f58])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_partfun1(X0)) = k10_relat_1(k6_partfun1(X1),X0)
      | ~ v4_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f100,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f100,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k10_relat_1(k6_partfun1(X1),X0) ),
    inference(subsumption_resolution,[],[f98,f58])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k10_relat_1(k6_partfun1(X1),X0)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f86,f60])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_partfun1(X0),k1_relat_1(X1)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f85,f58])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_partfun1(X0),k1_relat_1(X1)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_partfun1(X0),k1_relat_1(X1)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_partfun1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f44,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f45,f38])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f90,plain,(
    sK2 != k10_relat_1(k6_partfun1(sK1),sK2) ),
    inference(subsumption_resolution,[],[f89,f56])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f89,plain,
    ( sK2 != k10_relat_1(k6_partfun1(sK1),sK2)
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(superposition,[],[f36,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f36,plain,(
    sK2 != k8_relset_1(sK1,sK1,k6_partfun1(sK1),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK2 != k8_relset_1(sK1,sK1,k6_partfun1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK2 != k8_relset_1(sK1,sK1,k6_partfun1(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(f81,plain,(
    r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f75,f72])).

fof(f72,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f70,f37])).

fof(f37,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f70,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1))
    | r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f47,f35])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f49,f62])).

fof(f62,plain,(
    ! [X0] : sP0(X0,k1_zfmisc_1(X0)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f1,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | r1_tarski(X3,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:12:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.48  % (11461)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (11471)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.49  % (11461)Refutation not found, incomplete strategy% (11461)------------------------------
% 0.21/0.49  % (11461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11461)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (11461)Memory used [KB]: 10618
% 0.21/0.49  % (11461)Time elapsed: 0.073 s
% 0.21/0.49  % (11461)------------------------------
% 0.21/0.49  % (11461)------------------------------
% 0.21/0.50  % (11471)Refutation not found, incomplete strategy% (11471)------------------------------
% 0.21/0.50  % (11471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11471)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (11471)Memory used [KB]: 10746
% 0.21/0.50  % (11471)Time elapsed: 0.071 s
% 0.21/0.50  % (11471)------------------------------
% 0.21/0.50  % (11471)------------------------------
% 0.21/0.55  % (11505)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.21/0.55  % (11505)Refutation not found, incomplete strategy% (11505)------------------------------
% 0.21/0.55  % (11505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (11505)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (11505)Memory used [KB]: 6140
% 0.21/0.55  % (11505)Time elapsed: 0.003 s
% 0.21/0.55  % (11505)------------------------------
% 0.21/0.55  % (11505)------------------------------
% 0.21/0.56  % (11465)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (11453)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (11473)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (11473)Refutation not found, incomplete strategy% (11473)------------------------------
% 0.21/0.57  % (11473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (11473)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (11473)Memory used [KB]: 10746
% 0.21/0.57  % (11473)Time elapsed: 0.052 s
% 0.21/0.57  % (11473)------------------------------
% 0.21/0.57  % (11473)------------------------------
% 0.21/0.57  % (11451)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.41/0.58  % (11470)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.58  % (11460)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.58  % (11452)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.58  % (11452)Refutation not found, incomplete strategy% (11452)------------------------------
% 1.41/0.58  % (11452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.58  % (11452)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.58  
% 1.41/0.58  % (11452)Memory used [KB]: 10618
% 1.41/0.58  % (11452)Time elapsed: 0.163 s
% 1.41/0.58  % (11452)------------------------------
% 1.41/0.58  % (11452)------------------------------
% 1.41/0.58  % (11456)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.58  % (11454)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.41/0.58  % (11458)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.58  % (11454)Refutation not found, incomplete strategy% (11454)------------------------------
% 1.41/0.58  % (11454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.58  % (11454)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.58  
% 1.41/0.58  % (11454)Memory used [KB]: 6140
% 1.41/0.58  % (11454)Time elapsed: 0.139 s
% 1.41/0.58  % (11454)------------------------------
% 1.41/0.58  % (11454)------------------------------
% 1.41/0.58  % (11474)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.58  % (11466)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.58  % (11480)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.58  % (11460)Refutation not found, incomplete strategy% (11460)------------------------------
% 1.41/0.58  % (11460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.58  % (11478)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.58  % (11466)Refutation not found, incomplete strategy% (11466)------------------------------
% 1.41/0.58  % (11466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.58  % (11460)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.58  
% 1.41/0.58  % (11460)Memory used [KB]: 10618
% 1.41/0.58  % (11460)Time elapsed: 0.142 s
% 1.41/0.58  % (11460)------------------------------
% 1.41/0.58  % (11460)------------------------------
% 1.41/0.59  % (11480)Refutation found. Thanks to Tanya!
% 1.41/0.59  % SZS status Theorem for theBenchmark
% 1.41/0.59  % SZS output start Proof for theBenchmark
% 1.41/0.59  fof(f133,plain,(
% 1.41/0.59    $false),
% 1.41/0.59    inference(unit_resulting_resolution,[],[f81,f120,f80])).
% 1.41/0.59  fof(f80,plain,(
% 1.41/0.59    ( ! [X0,X1] : (v4_relat_1(k6_partfun1(X0),X1) | ~r1_tarski(X0,X1)) )),
% 1.41/0.59    inference(subsumption_resolution,[],[f79,f58])).
% 1.41/0.59  fof(f58,plain,(
% 1.41/0.59    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 1.41/0.59    inference(definition_unfolding,[],[f40,f38])).
% 1.41/0.59  fof(f38,plain,(
% 1.41/0.59    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f12])).
% 1.41/0.59  fof(f12,axiom,(
% 1.41/0.59    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.41/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.41/0.59  fof(f40,plain,(
% 1.41/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.41/0.59    inference(cnf_transformation,[],[f15])).
% 1.41/0.59  fof(f15,plain,(
% 1.41/0.59    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 1.41/0.59    inference(pure_predicate_removal,[],[f9])).
% 1.41/0.59  fof(f9,axiom,(
% 1.41/0.59    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 1.41/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).
% 1.41/0.59  fof(f79,plain,(
% 1.41/0.59    ( ! [X0,X1] : (v4_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(k6_partfun1(X0)) | ~r1_tarski(X0,X1)) )),
% 1.41/0.59    inference(resolution,[],[f46,f57])).
% 1.41/0.59  fof(f57,plain,(
% 1.41/0.59    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 1.41/0.59    inference(definition_unfolding,[],[f41,f38])).
% 1.41/0.59  fof(f41,plain,(
% 1.41/0.59    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f15])).
% 1.41/0.59  fof(f46,plain,(
% 1.41/0.59    ( ! [X2,X0,X1] : (~v4_relat_1(X2,X0) | v4_relat_1(X2,X1) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f20])).
% 1.41/0.59  fof(f20,plain,(
% 1.41/0.59    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 1.41/0.59    inference(flattening,[],[f19])).
% 1.41/0.59  fof(f19,plain,(
% 1.41/0.59    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 1.41/0.59    inference(ennf_transformation,[],[f6])).
% 1.41/0.59  fof(f6,axiom,(
% 1.41/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 1.41/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).
% 1.41/0.59  fof(f120,plain,(
% 1.41/0.59    ~v4_relat_1(k6_partfun1(sK2),sK1)),
% 1.41/0.59    inference(trivial_inequality_removal,[],[f118])).
% 1.41/0.59  fof(f118,plain,(
% 1.41/0.59    sK2 != sK2 | ~v4_relat_1(k6_partfun1(sK2),sK1)),
% 1.41/0.59    inference(superposition,[],[f90,f106])).
% 1.41/0.59  fof(f106,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X1),X0) = X0 | ~v4_relat_1(k6_partfun1(X0),X1)) )),
% 1.41/0.59    inference(forward_demodulation,[],[f105,f60])).
% 1.41/0.59  fof(f60,plain,(
% 1.41/0.59    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.41/0.59    inference(definition_unfolding,[],[f42,f38])).
% 1.41/0.59  fof(f42,plain,(
% 1.41/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.41/0.59    inference(cnf_transformation,[],[f7])).
% 1.41/0.59  fof(f7,axiom,(
% 1.41/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.41/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.41/0.59  fof(f105,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k1_relat_1(k6_partfun1(X0)) = k10_relat_1(k6_partfun1(X1),X0) | ~v4_relat_1(k6_partfun1(X0),X1)) )),
% 1.41/0.59    inference(subsumption_resolution,[],[f103,f58])).
% 1.41/0.59  fof(f103,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k1_relat_1(k6_partfun1(X0)) = k10_relat_1(k6_partfun1(X1),X0) | ~v4_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(k6_partfun1(X0))) )),
% 1.41/0.59    inference(superposition,[],[f100,f48])).
% 1.41/0.59  fof(f48,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f24])).
% 1.41/0.59  fof(f24,plain,(
% 1.41/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.41/0.59    inference(flattening,[],[f23])).
% 1.41/0.59  fof(f23,plain,(
% 1.41/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.41/0.59    inference(ennf_transformation,[],[f5])).
% 1.41/0.59  fof(f5,axiom,(
% 1.41/0.59    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.41/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.41/0.59  fof(f100,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k10_relat_1(k6_partfun1(X1),X0)) )),
% 1.41/0.59    inference(subsumption_resolution,[],[f98,f58])).
% 1.41/0.59  fof(f98,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_partfun1(X0),X1)) = k10_relat_1(k6_partfun1(X1),X0) | ~v1_relat_1(k6_partfun1(X0))) )),
% 1.41/0.59    inference(superposition,[],[f86,f60])).
% 1.41/0.59  fof(f86,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),k1_relat_1(X1)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.41/0.59    inference(subsumption_resolution,[],[f85,f58])).
% 1.41/0.59  fof(f85,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),k1_relat_1(X1)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(k6_partfun1(X0))) )),
% 1.41/0.59    inference(duplicate_literal_removal,[],[f84])).
% 1.41/0.59  fof(f84,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),k1_relat_1(X1)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(k6_partfun1(X0)) | ~v1_relat_1(X1)) )),
% 1.41/0.59    inference(superposition,[],[f44,f61])).
% 1.41/0.59  fof(f61,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.41/0.59    inference(definition_unfolding,[],[f45,f38])).
% 1.41/0.59  fof(f45,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f18])).
% 1.41/0.59  fof(f18,plain,(
% 1.41/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.41/0.59    inference(ennf_transformation,[],[f8])).
% 1.41/0.59  fof(f8,axiom,(
% 1.41/0.59    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.41/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.41/0.59  fof(f44,plain,(
% 1.41/0.59    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f17])).
% 1.41/0.59  fof(f17,plain,(
% 1.41/0.59    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.41/0.59    inference(ennf_transformation,[],[f4])).
% 1.41/0.59  fof(f4,axiom,(
% 1.41/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.41/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 1.41/0.59  fof(f90,plain,(
% 1.41/0.59    sK2 != k10_relat_1(k6_partfun1(sK1),sK2)),
% 1.41/0.59    inference(subsumption_resolution,[],[f89,f56])).
% 1.41/0.59  fof(f56,plain,(
% 1.41/0.59    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.41/0.59    inference(definition_unfolding,[],[f39,f38])).
% 1.41/0.59  fof(f39,plain,(
% 1.41/0.59    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.41/0.59    inference(cnf_transformation,[],[f11])).
% 1.41/0.59  fof(f11,axiom,(
% 1.41/0.59    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.41/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.41/0.59  fof(f89,plain,(
% 1.41/0.59    sK2 != k10_relat_1(k6_partfun1(sK1),sK2) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.41/0.59    inference(superposition,[],[f36,f55])).
% 1.41/0.59  fof(f55,plain,(
% 1.41/0.59    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.59    inference(cnf_transformation,[],[f25])).
% 1.41/0.59  fof(f25,plain,(
% 1.41/0.59    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.59    inference(ennf_transformation,[],[f10])).
% 1.41/0.59  fof(f10,axiom,(
% 1.41/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.41/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.41/0.59  fof(f36,plain,(
% 1.41/0.59    sK2 != k8_relset_1(sK1,sK1,k6_partfun1(sK1),sK2)),
% 1.41/0.59    inference(cnf_transformation,[],[f29])).
% 1.41/0.59  fof(f29,plain,(
% 1.41/0.59    sK2 != k8_relset_1(sK1,sK1,k6_partfun1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 1.41/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f28])).
% 1.41/0.59  fof(f28,plain,(
% 1.41/0.59    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK2 != k8_relset_1(sK1,sK1,k6_partfun1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 1.41/0.59    introduced(choice_axiom,[])).
% 1.41/0.59  fof(f16,plain,(
% 1.41/0.59    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.59    inference(ennf_transformation,[],[f14])).
% 1.41/0.59  fof(f14,negated_conjecture,(
% 1.41/0.59    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 1.41/0.59    inference(negated_conjecture,[],[f13])).
% 1.41/0.59  fof(f13,conjecture,(
% 1.41/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 1.41/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).
% 1.41/0.59  fof(f81,plain,(
% 1.41/0.59    r1_tarski(sK2,sK1)),
% 1.41/0.59    inference(resolution,[],[f75,f72])).
% 1.41/0.59  fof(f72,plain,(
% 1.41/0.59    r2_hidden(sK2,k1_zfmisc_1(sK1))),
% 1.41/0.59    inference(subsumption_resolution,[],[f70,f37])).
% 1.41/0.59  fof(f37,plain,(
% 1.41/0.59    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.41/0.59    inference(cnf_transformation,[],[f2])).
% 1.41/0.59  fof(f2,axiom,(
% 1.41/0.59    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.41/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.41/0.59  fof(f70,plain,(
% 1.41/0.59    v1_xboole_0(k1_zfmisc_1(sK1)) | r2_hidden(sK2,k1_zfmisc_1(sK1))),
% 1.41/0.59    inference(resolution,[],[f47,f35])).
% 1.41/0.59  fof(f35,plain,(
% 1.41/0.59    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 1.41/0.59    inference(cnf_transformation,[],[f29])).
% 1.41/0.59  fof(f47,plain,(
% 1.41/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f22])).
% 1.41/0.59  fof(f22,plain,(
% 1.41/0.59    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.41/0.59    inference(flattening,[],[f21])).
% 1.41/0.59  fof(f21,plain,(
% 1.41/0.59    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.41/0.59    inference(ennf_transformation,[],[f3])).
% 1.41/0.59  fof(f3,axiom,(
% 1.41/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.41/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.41/0.59  fof(f75,plain,(
% 1.41/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.41/0.59    inference(resolution,[],[f49,f62])).
% 1.41/0.59  fof(f62,plain,(
% 1.41/0.59    ( ! [X0] : (sP0(X0,k1_zfmisc_1(X0))) )),
% 1.41/0.59    inference(equality_resolution,[],[f53])).
% 1.41/0.59  fof(f53,plain,(
% 1.41/0.59    ( ! [X0,X1] : (sP0(X0,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.41/0.59    inference(cnf_transformation,[],[f34])).
% 1.41/0.59  fof(f34,plain,(
% 1.41/0.59    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_zfmisc_1(X0) != X1))),
% 1.41/0.59    inference(nnf_transformation,[],[f27])).
% 1.41/0.59  fof(f27,plain,(
% 1.41/0.59    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> sP0(X0,X1))),
% 1.41/0.59    inference(definition_folding,[],[f1,f26])).
% 1.41/0.59  fof(f26,plain,(
% 1.41/0.59    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.41/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.41/0.59  fof(f1,axiom,(
% 1.41/0.59    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.41/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.41/0.59  fof(f49,plain,(
% 1.41/0.59    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r2_hidden(X3,X1) | r1_tarski(X3,X0)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f33])).
% 1.41/0.59  fof(f33,plain,(
% 1.41/0.59    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 1.41/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 1.41/0.59  fof(f32,plain,(
% 1.41/0.59    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.41/0.59    introduced(choice_axiom,[])).
% 1.41/0.59  fof(f31,plain,(
% 1.41/0.59    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 1.41/0.59    inference(rectify,[],[f30])).
% 1.41/0.59  fof(f30,plain,(
% 1.41/0.59    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 1.41/0.59    inference(nnf_transformation,[],[f26])).
% 1.41/0.59  % SZS output end Proof for theBenchmark
% 1.41/0.59  % (11480)------------------------------
% 1.41/0.59  % (11480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.59  % (11480)Termination reason: Refutation
% 1.41/0.59  
% 1.41/0.59  % (11480)Memory used [KB]: 1791
% 1.41/0.59  % (11480)Time elapsed: 0.169 s
% 1.41/0.59  % (11480)------------------------------
% 1.41/0.59  % (11480)------------------------------
% 1.41/0.59  % (11466)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.59  
% 1.41/0.59  % (11466)Memory used [KB]: 6140
% 1.41/0.59  % (11466)Time elapsed: 0.005 s
% 1.41/0.59  % (11466)------------------------------
% 1.41/0.59  % (11466)------------------------------
% 1.41/0.59  % (11477)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.59  % (11463)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.59  % (11469)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.59  % (11472)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.77/0.59  % (11459)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.77/0.59  % (11472)Refutation not found, incomplete strategy% (11472)------------------------------
% 1.77/0.59  % (11472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.59  % (11472)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.59  
% 1.77/0.59  % (11472)Memory used [KB]: 1663
% 1.77/0.59  % (11472)Time elapsed: 0.177 s
% 1.77/0.59  % (11472)------------------------------
% 1.77/0.59  % (11472)------------------------------
% 1.77/0.59  % (11459)Refutation not found, incomplete strategy% (11459)------------------------------
% 1.77/0.59  % (11459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.59  % (11459)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.59  
% 1.77/0.59  % (11459)Memory used [KB]: 10618
% 1.77/0.59  % (11459)Time elapsed: 0.179 s
% 1.77/0.59  % (11459)------------------------------
% 1.77/0.59  % (11459)------------------------------
% 1.77/0.59  % (11458)Refutation not found, incomplete strategy% (11458)------------------------------
% 1.77/0.59  % (11458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.59  % (11449)Success in time 0.226 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 13:06:04 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  178 (2187 expanded)
%              Number of leaves         :   21 ( 545 expanded)
%              Depth                    :   33
%              Number of atoms          :  511 (12255 expanded)
%              Number of equality atoms :  109 (2901 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f803,plain,(
    $false ),
    inference(subsumption_resolution,[],[f795,f64])).

fof(f64,plain,(
    r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3))
      | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) )
    & r1_tarski(sK3,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v3_funct_2(sK4,sK2,sK2)
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f51])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
          | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
        & r1_tarski(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
   => ( ( sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3))
        | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) )
      & r1_tarski(sK3,sK2)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v3_funct_2(sK4,sK2,sK2)
      & v1_funct_2(sK4,sK2,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

fof(f795,plain,(
    ~ r1_tarski(sK3,sK2) ),
    inference(backward_demodulation,[],[f622,f779])).

fof(f779,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(backward_demodulation,[],[f211,f762])).

fof(f762,plain,(
    sK2 = k10_relat_1(sK4,sK2) ),
    inference(backward_demodulation,[],[f455,f755])).

fof(f755,plain,(
    sK2 = k1_relat_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f748,f305])).

fof(f305,plain,(
    r1_tarski(k1_relat_1(k2_funct_1(sK4)),sK2) ),
    inference(subsumption_resolution,[],[f304,f287])).

fof(f287,plain,(
    v1_relat_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f278,f69])).

fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f278,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(resolution,[],[f229,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f229,plain,(
    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(subsumption_resolution,[],[f226,f130])).

fof(f130,plain,(
    sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f129,f60])).

fof(f60,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f129,plain,
    ( sP0(sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f128,f61])).

fof(f61,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f128,plain,
    ( sP0(sK2,sK4)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f120,f62])).

fof(f62,plain,(
    v3_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f120,plain,
    ( sP0(sK2,sK4)
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f63,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(definition_folding,[],[f39,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f63,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f52])).

fof(f226,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ sP0(sK2,sK4) ),
    inference(superposition,[],[f82,f133])).

fof(f133,plain,(
    k2_funct_1(sK4) = k2_funct_2(sK2,sK4) ),
    inference(subsumption_resolution,[],[f132,f60])).

fof(f132,plain,
    ( k2_funct_1(sK4) = k2_funct_2(sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f131,f61])).

fof(f131,plain,
    ( k2_funct_1(sK4) = k2_funct_2(sK2,sK4)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f121,f62])).

fof(f121,plain,
    ( k2_funct_1(sK4) = k2_funct_2(sK2,sK4)
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f63,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

% (28068)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% (28065)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (28052)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (28048)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (28067)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f36,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f304,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK4)),sK2)
    | ~ v1_relat_1(k2_funct_1(sK4)) ),
    inference(resolution,[],[f276,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f276,plain,(
    v4_relat_1(k2_funct_1(sK4),sK2) ),
    inference(resolution,[],[f229,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f748,plain,
    ( sK2 = k1_relat_1(k2_funct_1(sK4))
    | ~ r1_tarski(k1_relat_1(k2_funct_1(sK4)),sK2) ),
    inference(resolution,[],[f740,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f740,plain,(
    r1_tarski(sK2,k1_relat_1(k2_funct_1(sK4))) ),
    inference(forward_demodulation,[],[f734,f478])).

fof(f478,plain,(
    k1_relat_1(k2_funct_1(sK4)) = k9_relat_1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f477,f305])).

fof(f477,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1(sK4)),sK2)
    | k1_relat_1(k2_funct_1(sK4)) = k9_relat_1(sK4,sK2) ),
    inference(forward_demodulation,[],[f476,f177])).

fof(f177,plain,(
    sK2 = k2_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f176,f136])).

fof(f136,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f127,f69])).

fof(f127,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(resolution,[],[f63,f68])).

fof(f176,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f175,f126])).

fof(f126,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f63,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f175,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ v5_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f166,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f166,plain,(
    v2_funct_2(sK4,sK2) ),
    inference(resolution,[],[f135,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP1(X1,X2) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ sP1(X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f135,plain,(
    sP1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f134,f60])).

fof(f134,plain,
    ( sP1(sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f124,f62])).

fof(f124,plain,
    ( sP1(sK2,sK4)
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f63,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f44,f49])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f476,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k9_relat_1(sK4,sK2)
    | ~ r1_tarski(k1_relat_1(k2_funct_1(sK4)),k2_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f475,f136])).

fof(f475,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k9_relat_1(sK4,sK2)
    | ~ r1_tarski(k1_relat_1(k2_funct_1(sK4)),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f474,f60])).

fof(f474,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k9_relat_1(sK4,sK2)
    | ~ r1_tarski(k1_relat_1(k2_funct_1(sK4)),k2_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f74,f455])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f734,plain,(
    r1_tarski(sK2,k9_relat_1(sK4,sK2)) ),
    inference(resolution,[],[f260,f157])).

fof(f157,plain,(
    r1_tarski(k1_relat_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f156,f136])).

fof(f156,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f125,f71])).

fof(f125,plain,(
    v4_relat_1(sK4,sK2) ),
    inference(resolution,[],[f63,f88])).

fof(f260,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK4),X1)
      | r1_tarski(sK2,k9_relat_1(sK4,X1)) ) ),
    inference(subsumption_resolution,[],[f257,f136])).

fof(f257,plain,(
    ! [X1] :
      ( r1_tarski(sK2,k9_relat_1(sK4,X1))
      | ~ r1_tarski(k1_relat_1(sK4),X1)
      | ~ v1_relat_1(sK4) ) ),
    inference(superposition,[],[f87,f252])).

fof(f252,plain,(
    sK2 = k9_relat_1(sK4,k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f251,f98])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f251,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = k9_relat_1(sK4,k1_relat_1(sK4)) ),
    inference(forward_demodulation,[],[f250,f177])).

fof(f250,plain,
    ( sK2 = k9_relat_1(sK4,k1_relat_1(sK4))
    | ~ r1_tarski(sK2,k2_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f249,f136])).

fof(f249,plain,
    ( sK2 = k9_relat_1(sK4,k1_relat_1(sK4))
    | ~ r1_tarski(sK2,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f248,f60])).

fof(f248,plain,
    ( sK2 = k9_relat_1(sK4,k1_relat_1(sK4))
    | ~ r1_tarski(sK2,k2_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f74,f211])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f455,plain,(
    sK2 = k10_relat_1(sK4,k1_relat_1(k2_funct_1(sK4))) ),
    inference(forward_demodulation,[],[f454,f329])).

fof(f329,plain,(
    sK2 = k2_relat_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f328,f287])).

fof(f328,plain,
    ( sK2 = k2_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f327,f277])).

fof(f277,plain,(
    v5_relat_1(k2_funct_1(sK4),sK2) ),
    inference(resolution,[],[f229,f89])).

fof(f327,plain,
    ( sK2 = k2_relat_1(k2_funct_1(sK4))
    | ~ v5_relat_1(k2_funct_1(sK4),sK2)
    | ~ v1_relat_1(k2_funct_1(sK4)) ),
    inference(resolution,[],[f318,f76])).

fof(f318,plain,(
    v2_funct_2(k2_funct_1(sK4),sK2) ),
    inference(resolution,[],[f286,f92])).

fof(f286,plain,(
    sP1(sK2,k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f285,f192])).

fof(f192,plain,(
    v1_funct_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f191,f60])).

fof(f191,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f190,f61])).

fof(f190,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f189,f62])).

fof(f189,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f188,f63])).

fof(f188,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f160,f78])).

fof(f160,plain,(
    v1_funct_1(k2_funct_2(sK2,sK4)) ),
    inference(resolution,[],[f130,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f285,plain,
    ( sP1(sK2,k2_funct_1(sK4))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f275,f228])).

fof(f228,plain,(
    v3_funct_2(k2_funct_1(sK4),sK2,sK2) ),
    inference(subsumption_resolution,[],[f225,f130])).

fof(f225,plain,
    ( v3_funct_2(k2_funct_1(sK4),sK2,sK2)
    | ~ sP0(sK2,sK4) ),
    inference(superposition,[],[f81,f133])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f275,plain,
    ( sP1(sK2,k2_funct_1(sK4))
    | ~ v3_funct_2(k2_funct_1(sK4),sK2,sK2)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(resolution,[],[f229,f93])).

fof(f454,plain,(
    k2_relat_1(k2_funct_1(sK4)) = k10_relat_1(sK4,k1_relat_1(k2_funct_1(sK4))) ),
    inference(subsumption_resolution,[],[f446,f287])).

fof(f446,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k10_relat_1(sK4,k1_relat_1(k2_funct_1(sK4)))
    | ~ v1_relat_1(k2_funct_1(sK4)) ),
    inference(superposition,[],[f419,f67])).

fof(f67,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f419,plain,(
    ! [X6] : k10_relat_1(sK4,X6) = k9_relat_1(k2_funct_1(sK4),X6) ),
    inference(subsumption_resolution,[],[f418,f136])).

fof(f418,plain,(
    ! [X6] :
      ( k10_relat_1(sK4,X6) = k9_relat_1(k2_funct_1(sK4),X6)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f104,f165])).

fof(f165,plain,(
    v2_funct_1(sK4) ),
    inference(resolution,[],[f135,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f104,plain,(
    ! [X6] :
      ( k10_relat_1(sK4,X6) = k9_relat_1(k2_funct_1(sK4),X6)
      | ~ v2_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f60,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f211,plain,(
    k1_relat_1(sK4) = k10_relat_1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f205,f136])).

fof(f205,plain,
    ( k1_relat_1(sK4) = k10_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f66,f177])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f622,plain,(
    ~ r1_tarski(sK3,k1_relat_1(sK4)) ),
    inference(trivial_inequality_removal,[],[f616])).

fof(f616,plain,
    ( sK3 != sK3
    | ~ r1_tarski(sK3,k1_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f360,f539])).

fof(f539,plain,(
    sK3 = k9_relat_1(sK4,k10_relat_1(sK4,sK3)) ),
    inference(resolution,[],[f503,f64])).

fof(f503,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,sK2)
      | k9_relat_1(sK4,k10_relat_1(sK4,X5)) = X5 ) ),
    inference(forward_demodulation,[],[f502,f177])).

fof(f502,plain,(
    ! [X5] :
      ( k9_relat_1(sK4,k10_relat_1(sK4,X5)) = X5
      | ~ r1_tarski(X5,k2_relat_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f103,f136])).

fof(f103,plain,(
    ! [X5] :
      ( k9_relat_1(sK4,k10_relat_1(sK4,X5)) = X5
      | ~ r1_tarski(X5,k2_relat_1(sK4))
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f60,f74])).

fof(f360,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK4))
    | sK3 != k9_relat_1(sK4,k10_relat_1(sK4,sK3)) ),
    inference(forward_demodulation,[],[f359,f122])).

fof(f122,plain,(
    ! [X0] : k7_relset_1(sK2,sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(resolution,[],[f63,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f359,plain,
    ( sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3))
    | ~ r1_tarski(sK3,k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f358,f136])).

fof(f358,plain,
    ( sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3))
    | ~ r1_tarski(sK3,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f357,f60])).

fof(f357,plain,
    ( sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3))
    | ~ r1_tarski(sK3,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f353,f165])).

fof(f353,plain,
    ( sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3))
    | ~ v2_funct_1(sK4)
    | ~ r1_tarski(sK3,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(trivial_inequality_removal,[],[f352])).

fof(f352,plain,
    ( sK3 != sK3
    | sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3))
    | ~ v2_funct_1(sK4)
    | ~ r1_tarski(sK3,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f326,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f326,plain,
    ( sK3 != k10_relat_1(sK4,k9_relat_1(sK4,sK3))
    | sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3)) ),
    inference(forward_demodulation,[],[f325,f123])).

fof(f123,plain,(
    ! [X1] : k8_relset_1(sK2,sK2,sK4,X1) = k10_relat_1(sK4,X1) ),
    inference(resolution,[],[f63,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f325,plain,
    ( sK3 != k10_relat_1(sK4,k9_relat_1(sK4,sK3))
    | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) ),
    inference(backward_demodulation,[],[f270,f123])).

fof(f270,plain,
    ( sK3 != k8_relset_1(sK2,sK2,sK4,k9_relat_1(sK4,sK3))
    | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) ),
    inference(backward_demodulation,[],[f65,f122])).

fof(f65,plain,
    ( sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3))
    | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (28062)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.50  % (28054)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.54  % (28055)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.54  % (28051)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.56  % (28049)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.56  % (28047)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.56  % (28059)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.57  % (28070)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.48/0.57  % (28057)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.48/0.57  % (28056)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.48/0.57  % (28055)Refutation found. Thanks to Tanya!
% 1.48/0.57  % SZS status Theorem for theBenchmark
% 1.48/0.57  % SZS output start Proof for theBenchmark
% 1.48/0.57  fof(f803,plain,(
% 1.48/0.57    $false),
% 1.48/0.57    inference(subsumption_resolution,[],[f795,f64])).
% 1.48/0.57  fof(f64,plain,(
% 1.48/0.57    r1_tarski(sK3,sK2)),
% 1.48/0.57    inference(cnf_transformation,[],[f52])).
% 1.48/0.57  fof(f52,plain,(
% 1.48/0.57    (sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3))) & r1_tarski(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK4,sK2,sK2) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)),
% 1.48/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f51])).
% 1.48/0.57  fof(f51,plain,(
% 1.48/0.57    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3))) & r1_tarski(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK4,sK2,sK2) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4))),
% 1.48/0.57    introduced(choice_axiom,[])).
% 1.48/0.57  fof(f22,plain,(
% 1.48/0.57    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 1.48/0.57    inference(flattening,[],[f21])).
% 1.48/0.57  fof(f21,plain,(
% 1.48/0.57    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 1.48/0.57    inference(ennf_transformation,[],[f20])).
% 1.48/0.57  fof(f20,negated_conjecture,(
% 1.48/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 1.48/0.57    inference(negated_conjecture,[],[f19])).
% 1.48/0.57  fof(f19,conjecture,(
% 1.48/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).
% 1.48/0.57  fof(f795,plain,(
% 1.48/0.57    ~r1_tarski(sK3,sK2)),
% 1.48/0.57    inference(backward_demodulation,[],[f622,f779])).
% 1.48/0.57  fof(f779,plain,(
% 1.48/0.57    sK2 = k1_relat_1(sK4)),
% 1.48/0.57    inference(backward_demodulation,[],[f211,f762])).
% 1.48/0.57  fof(f762,plain,(
% 1.48/0.57    sK2 = k10_relat_1(sK4,sK2)),
% 1.48/0.57    inference(backward_demodulation,[],[f455,f755])).
% 1.48/0.57  fof(f755,plain,(
% 1.48/0.57    sK2 = k1_relat_1(k2_funct_1(sK4))),
% 1.48/0.57    inference(subsumption_resolution,[],[f748,f305])).
% 1.48/0.57  fof(f305,plain,(
% 1.48/0.57    r1_tarski(k1_relat_1(k2_funct_1(sK4)),sK2)),
% 1.48/0.57    inference(subsumption_resolution,[],[f304,f287])).
% 1.48/0.57  fof(f287,plain,(
% 1.48/0.57    v1_relat_1(k2_funct_1(sK4))),
% 1.48/0.57    inference(subsumption_resolution,[],[f278,f69])).
% 1.48/0.57  fof(f69,plain,(
% 1.48/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f4])).
% 1.48/0.57  fof(f4,axiom,(
% 1.48/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.48/0.57  fof(f278,plain,(
% 1.48/0.57    v1_relat_1(k2_funct_1(sK4)) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))),
% 1.48/0.57    inference(resolution,[],[f229,f68])).
% 1.48/0.57  fof(f68,plain,(
% 1.48/0.57    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f25])).
% 1.48/0.57  fof(f25,plain,(
% 1.48/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.48/0.57    inference(ennf_transformation,[],[f2])).
% 1.48/0.57  fof(f2,axiom,(
% 1.48/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.48/0.57  fof(f229,plain,(
% 1.48/0.57    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 1.48/0.57    inference(subsumption_resolution,[],[f226,f130])).
% 1.48/0.57  fof(f130,plain,(
% 1.48/0.57    sP0(sK2,sK4)),
% 1.48/0.57    inference(subsumption_resolution,[],[f129,f60])).
% 1.48/0.57  fof(f60,plain,(
% 1.48/0.57    v1_funct_1(sK4)),
% 1.48/0.57    inference(cnf_transformation,[],[f52])).
% 1.48/0.57  fof(f129,plain,(
% 1.48/0.57    sP0(sK2,sK4) | ~v1_funct_1(sK4)),
% 1.48/0.57    inference(subsumption_resolution,[],[f128,f61])).
% 1.48/0.57  fof(f61,plain,(
% 1.48/0.57    v1_funct_2(sK4,sK2,sK2)),
% 1.48/0.57    inference(cnf_transformation,[],[f52])).
% 1.48/0.57  fof(f128,plain,(
% 1.48/0.57    sP0(sK2,sK4) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 1.48/0.57    inference(subsumption_resolution,[],[f120,f62])).
% 1.48/0.57  fof(f62,plain,(
% 1.48/0.57    v3_funct_2(sK4,sK2,sK2)),
% 1.48/0.57    inference(cnf_transformation,[],[f52])).
% 1.48/0.57  fof(f120,plain,(
% 1.48/0.57    sP0(sK2,sK4) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 1.48/0.57    inference(resolution,[],[f63,f83])).
% 1.48/0.57  fof(f83,plain,(
% 1.48/0.57    ( ! [X0,X1] : (sP0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f48])).
% 1.48/0.57  fof(f48,plain,(
% 1.48/0.57    ! [X0,X1] : (sP0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.48/0.57    inference(definition_folding,[],[f39,f47])).
% 1.48/0.57  fof(f47,plain,(
% 1.48/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~sP0(X0,X1))),
% 1.48/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.48/0.57  fof(f39,plain,(
% 1.48/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.48/0.57    inference(flattening,[],[f38])).
% 1.48/0.57  fof(f38,plain,(
% 1.48/0.57    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.48/0.57    inference(ennf_transformation,[],[f17])).
% 1.48/0.57  fof(f17,axiom,(
% 1.48/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 1.48/0.57  fof(f63,plain,(
% 1.48/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 1.48/0.57    inference(cnf_transformation,[],[f52])).
% 1.48/0.57  fof(f226,plain,(
% 1.48/0.57    m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~sP0(sK2,sK4)),
% 1.48/0.57    inference(superposition,[],[f82,f133])).
% 1.48/0.57  fof(f133,plain,(
% 1.48/0.57    k2_funct_1(sK4) = k2_funct_2(sK2,sK4)),
% 1.48/0.57    inference(subsumption_resolution,[],[f132,f60])).
% 1.48/0.57  fof(f132,plain,(
% 1.48/0.57    k2_funct_1(sK4) = k2_funct_2(sK2,sK4) | ~v1_funct_1(sK4)),
% 1.48/0.57    inference(subsumption_resolution,[],[f131,f61])).
% 1.48/0.57  fof(f131,plain,(
% 1.48/0.57    k2_funct_1(sK4) = k2_funct_2(sK2,sK4) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 1.48/0.57    inference(subsumption_resolution,[],[f121,f62])).
% 1.48/0.57  fof(f121,plain,(
% 1.48/0.57    k2_funct_1(sK4) = k2_funct_2(sK2,sK4) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 1.48/0.57    inference(resolution,[],[f63,f78])).
% 1.48/0.57  fof(f78,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f37])).
% 1.48/0.57  fof(f37,plain,(
% 1.48/0.57    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.48/0.57    inference(flattening,[],[f36])).
% 1.48/0.57  % (28068)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.48/0.57  % (28065)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.48/0.57  % (28052)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.48/0.58  % (28048)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.48/0.58  % (28067)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.82/0.59  fof(f36,plain,(
% 1.82/0.59    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.82/0.59    inference(ennf_transformation,[],[f18])).
% 1.82/0.59  fof(f18,axiom,(
% 1.82/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.82/0.59  fof(f82,plain,(
% 1.82/0.59    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~sP0(X0,X1)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f55])).
% 1.82/0.59  fof(f55,plain,(
% 1.82/0.59    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~sP0(X0,X1))),
% 1.82/0.59    inference(nnf_transformation,[],[f47])).
% 1.82/0.59  fof(f304,plain,(
% 1.82/0.59    r1_tarski(k1_relat_1(k2_funct_1(sK4)),sK2) | ~v1_relat_1(k2_funct_1(sK4))),
% 1.82/0.59    inference(resolution,[],[f276,f71])).
% 1.82/0.59  fof(f71,plain,(
% 1.82/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f53])).
% 1.82/0.59  fof(f53,plain,(
% 1.82/0.59    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.82/0.59    inference(nnf_transformation,[],[f27])).
% 1.82/0.59  fof(f27,plain,(
% 1.82/0.59    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.82/0.59    inference(ennf_transformation,[],[f3])).
% 1.82/0.59  fof(f3,axiom,(
% 1.82/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.82/0.59  fof(f276,plain,(
% 1.82/0.59    v4_relat_1(k2_funct_1(sK4),sK2)),
% 1.82/0.59    inference(resolution,[],[f229,f88])).
% 1.82/0.59  fof(f88,plain,(
% 1.82/0.59    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.82/0.59    inference(cnf_transformation,[],[f42])).
% 1.82/0.59  fof(f42,plain,(
% 1.82/0.59    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.59    inference(ennf_transformation,[],[f12])).
% 1.82/0.59  fof(f12,axiom,(
% 1.82/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.82/0.59  fof(f748,plain,(
% 1.82/0.59    sK2 = k1_relat_1(k2_funct_1(sK4)) | ~r1_tarski(k1_relat_1(k2_funct_1(sK4)),sK2)),
% 1.82/0.59    inference(resolution,[],[f740,f86])).
% 1.82/0.59  fof(f86,plain,(
% 1.82/0.59    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f57])).
% 1.82/0.59  fof(f57,plain,(
% 1.82/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.82/0.59    inference(flattening,[],[f56])).
% 1.82/0.59  fof(f56,plain,(
% 1.82/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.82/0.59    inference(nnf_transformation,[],[f1])).
% 1.82/0.59  fof(f1,axiom,(
% 1.82/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.82/0.59  fof(f740,plain,(
% 1.82/0.59    r1_tarski(sK2,k1_relat_1(k2_funct_1(sK4)))),
% 1.82/0.59    inference(forward_demodulation,[],[f734,f478])).
% 1.82/0.59  fof(f478,plain,(
% 1.82/0.59    k1_relat_1(k2_funct_1(sK4)) = k9_relat_1(sK4,sK2)),
% 1.82/0.59    inference(subsumption_resolution,[],[f477,f305])).
% 1.82/0.59  fof(f477,plain,(
% 1.82/0.59    ~r1_tarski(k1_relat_1(k2_funct_1(sK4)),sK2) | k1_relat_1(k2_funct_1(sK4)) = k9_relat_1(sK4,sK2)),
% 1.82/0.59    inference(forward_demodulation,[],[f476,f177])).
% 1.82/0.59  fof(f177,plain,(
% 1.82/0.59    sK2 = k2_relat_1(sK4)),
% 1.82/0.59    inference(subsumption_resolution,[],[f176,f136])).
% 1.82/0.59  fof(f136,plain,(
% 1.82/0.59    v1_relat_1(sK4)),
% 1.82/0.59    inference(subsumption_resolution,[],[f127,f69])).
% 1.82/0.59  fof(f127,plain,(
% 1.82/0.59    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))),
% 1.82/0.59    inference(resolution,[],[f63,f68])).
% 1.82/0.59  fof(f176,plain,(
% 1.82/0.59    sK2 = k2_relat_1(sK4) | ~v1_relat_1(sK4)),
% 1.82/0.59    inference(subsumption_resolution,[],[f175,f126])).
% 1.82/0.59  fof(f126,plain,(
% 1.82/0.59    v5_relat_1(sK4,sK2)),
% 1.82/0.59    inference(resolution,[],[f63,f89])).
% 1.82/0.59  fof(f89,plain,(
% 1.82/0.59    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.82/0.59    inference(cnf_transformation,[],[f42])).
% 1.82/0.59  fof(f175,plain,(
% 1.82/0.59    sK2 = k2_relat_1(sK4) | ~v5_relat_1(sK4,sK2) | ~v1_relat_1(sK4)),
% 1.82/0.59    inference(resolution,[],[f166,f76])).
% 1.82/0.59  fof(f76,plain,(
% 1.82/0.59    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f54])).
% 1.82/0.59  fof(f54,plain,(
% 1.82/0.59    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.82/0.59    inference(nnf_transformation,[],[f35])).
% 1.82/0.59  fof(f35,plain,(
% 1.82/0.59    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.82/0.59    inference(flattening,[],[f34])).
% 1.82/0.59  fof(f34,plain,(
% 1.82/0.59    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.82/0.59    inference(ennf_transformation,[],[f16])).
% 1.82/0.59  fof(f16,axiom,(
% 1.82/0.59    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.82/0.59  fof(f166,plain,(
% 1.82/0.59    v2_funct_2(sK4,sK2)),
% 1.82/0.59    inference(resolution,[],[f135,f92])).
% 1.82/0.59  fof(f92,plain,(
% 1.82/0.59    ( ! [X0,X1] : (v2_funct_2(X1,X0) | ~sP1(X0,X1)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f59])).
% 1.82/0.59  fof(f59,plain,(
% 1.82/0.59    ! [X0,X1] : ((v2_funct_2(X1,X0) & v2_funct_1(X1) & v1_funct_1(X1)) | ~sP1(X0,X1))),
% 1.82/0.59    inference(rectify,[],[f58])).
% 1.82/0.59  fof(f58,plain,(
% 1.82/0.59    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP1(X1,X2))),
% 1.82/0.59    inference(nnf_transformation,[],[f49])).
% 1.82/0.59  fof(f49,plain,(
% 1.82/0.59    ! [X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~sP1(X1,X2))),
% 1.82/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.82/0.59  fof(f135,plain,(
% 1.82/0.59    sP1(sK2,sK4)),
% 1.82/0.59    inference(subsumption_resolution,[],[f134,f60])).
% 1.82/0.59  fof(f134,plain,(
% 1.82/0.59    sP1(sK2,sK4) | ~v1_funct_1(sK4)),
% 1.82/0.59    inference(subsumption_resolution,[],[f124,f62])).
% 1.82/0.59  fof(f124,plain,(
% 1.82/0.59    sP1(sK2,sK4) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 1.82/0.59    inference(resolution,[],[f63,f93])).
% 1.82/0.59  fof(f93,plain,(
% 1.82/0.59    ( ! [X2,X0,X1] : (sP1(X1,X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.82/0.59    inference(cnf_transformation,[],[f50])).
% 1.82/0.59  fof(f50,plain,(
% 1.82/0.59    ! [X0,X1,X2] : (sP1(X1,X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.59    inference(definition_folding,[],[f44,f49])).
% 1.82/0.59  fof(f44,plain,(
% 1.82/0.59    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.59    inference(flattening,[],[f43])).
% 1.82/0.59  fof(f43,plain,(
% 1.82/0.59    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.59    inference(ennf_transformation,[],[f15])).
% 1.82/0.59  fof(f15,axiom,(
% 1.82/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.82/0.59  fof(f476,plain,(
% 1.82/0.59    k1_relat_1(k2_funct_1(sK4)) = k9_relat_1(sK4,sK2) | ~r1_tarski(k1_relat_1(k2_funct_1(sK4)),k2_relat_1(sK4))),
% 1.82/0.59    inference(subsumption_resolution,[],[f475,f136])).
% 1.82/0.59  fof(f475,plain,(
% 1.82/0.59    k1_relat_1(k2_funct_1(sK4)) = k9_relat_1(sK4,sK2) | ~r1_tarski(k1_relat_1(k2_funct_1(sK4)),k2_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 1.82/0.59    inference(subsumption_resolution,[],[f474,f60])).
% 1.82/0.59  fof(f474,plain,(
% 1.82/0.59    k1_relat_1(k2_funct_1(sK4)) = k9_relat_1(sK4,sK2) | ~r1_tarski(k1_relat_1(k2_funct_1(sK4)),k2_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.82/0.59    inference(superposition,[],[f74,f455])).
% 1.82/0.59  fof(f74,plain,(
% 1.82/0.59    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f31])).
% 1.82/0.59  fof(f31,plain,(
% 1.82/0.59    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.82/0.59    inference(flattening,[],[f30])).
% 1.82/0.59  fof(f30,plain,(
% 1.82/0.59    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.82/0.59    inference(ennf_transformation,[],[f9])).
% 1.82/0.59  fof(f9,axiom,(
% 1.82/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 1.82/0.59  fof(f734,plain,(
% 1.82/0.59    r1_tarski(sK2,k9_relat_1(sK4,sK2))),
% 1.82/0.59    inference(resolution,[],[f260,f157])).
% 1.82/0.59  fof(f157,plain,(
% 1.82/0.59    r1_tarski(k1_relat_1(sK4),sK2)),
% 1.82/0.59    inference(subsumption_resolution,[],[f156,f136])).
% 1.82/0.59  fof(f156,plain,(
% 1.82/0.59    r1_tarski(k1_relat_1(sK4),sK2) | ~v1_relat_1(sK4)),
% 1.82/0.59    inference(resolution,[],[f125,f71])).
% 1.82/0.59  fof(f125,plain,(
% 1.82/0.59    v4_relat_1(sK4,sK2)),
% 1.82/0.59    inference(resolution,[],[f63,f88])).
% 1.82/0.59  fof(f260,plain,(
% 1.82/0.59    ( ! [X1] : (~r1_tarski(k1_relat_1(sK4),X1) | r1_tarski(sK2,k9_relat_1(sK4,X1))) )),
% 1.82/0.59    inference(subsumption_resolution,[],[f257,f136])).
% 1.82/0.59  fof(f257,plain,(
% 1.82/0.59    ( ! [X1] : (r1_tarski(sK2,k9_relat_1(sK4,X1)) | ~r1_tarski(k1_relat_1(sK4),X1) | ~v1_relat_1(sK4)) )),
% 1.82/0.59    inference(superposition,[],[f87,f252])).
% 1.82/0.59  fof(f252,plain,(
% 1.82/0.59    sK2 = k9_relat_1(sK4,k1_relat_1(sK4))),
% 1.82/0.59    inference(subsumption_resolution,[],[f251,f98])).
% 1.82/0.59  fof(f98,plain,(
% 1.82/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.82/0.59    inference(equality_resolution,[],[f84])).
% 1.82/0.59  fof(f84,plain,(
% 1.82/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.82/0.59    inference(cnf_transformation,[],[f57])).
% 1.82/0.59  fof(f251,plain,(
% 1.82/0.59    ~r1_tarski(sK2,sK2) | sK2 = k9_relat_1(sK4,k1_relat_1(sK4))),
% 1.82/0.59    inference(forward_demodulation,[],[f250,f177])).
% 1.82/0.59  fof(f250,plain,(
% 1.82/0.59    sK2 = k9_relat_1(sK4,k1_relat_1(sK4)) | ~r1_tarski(sK2,k2_relat_1(sK4))),
% 1.82/0.59    inference(subsumption_resolution,[],[f249,f136])).
% 1.82/0.59  fof(f249,plain,(
% 1.82/0.59    sK2 = k9_relat_1(sK4,k1_relat_1(sK4)) | ~r1_tarski(sK2,k2_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 1.82/0.59    inference(subsumption_resolution,[],[f248,f60])).
% 1.82/0.59  fof(f248,plain,(
% 1.82/0.59    sK2 = k9_relat_1(sK4,k1_relat_1(sK4)) | ~r1_tarski(sK2,k2_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.82/0.59    inference(superposition,[],[f74,f211])).
% 1.82/0.59  fof(f87,plain,(
% 1.82/0.59    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f41])).
% 1.82/0.59  fof(f41,plain,(
% 1.82/0.59    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.82/0.59    inference(flattening,[],[f40])).
% 1.82/0.59  fof(f40,plain,(
% 1.82/0.59    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.82/0.59    inference(ennf_transformation,[],[f7])).
% 1.82/0.59  fof(f7,axiom,(
% 1.82/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 1.82/0.59  fof(f455,plain,(
% 1.82/0.59    sK2 = k10_relat_1(sK4,k1_relat_1(k2_funct_1(sK4)))),
% 1.82/0.59    inference(forward_demodulation,[],[f454,f329])).
% 1.82/0.59  fof(f329,plain,(
% 1.82/0.59    sK2 = k2_relat_1(k2_funct_1(sK4))),
% 1.82/0.59    inference(subsumption_resolution,[],[f328,f287])).
% 1.82/0.59  fof(f328,plain,(
% 1.82/0.59    sK2 = k2_relat_1(k2_funct_1(sK4)) | ~v1_relat_1(k2_funct_1(sK4))),
% 1.82/0.59    inference(subsumption_resolution,[],[f327,f277])).
% 1.82/0.59  fof(f277,plain,(
% 1.82/0.59    v5_relat_1(k2_funct_1(sK4),sK2)),
% 1.82/0.59    inference(resolution,[],[f229,f89])).
% 1.82/0.59  fof(f327,plain,(
% 1.82/0.59    sK2 = k2_relat_1(k2_funct_1(sK4)) | ~v5_relat_1(k2_funct_1(sK4),sK2) | ~v1_relat_1(k2_funct_1(sK4))),
% 1.82/0.59    inference(resolution,[],[f318,f76])).
% 1.82/0.59  fof(f318,plain,(
% 1.82/0.59    v2_funct_2(k2_funct_1(sK4),sK2)),
% 1.82/0.59    inference(resolution,[],[f286,f92])).
% 1.82/0.59  fof(f286,plain,(
% 1.82/0.59    sP1(sK2,k2_funct_1(sK4))),
% 1.82/0.59    inference(subsumption_resolution,[],[f285,f192])).
% 1.82/0.59  fof(f192,plain,(
% 1.82/0.59    v1_funct_1(k2_funct_1(sK4))),
% 1.82/0.59    inference(subsumption_resolution,[],[f191,f60])).
% 1.82/0.59  fof(f191,plain,(
% 1.82/0.59    v1_funct_1(k2_funct_1(sK4)) | ~v1_funct_1(sK4)),
% 1.82/0.59    inference(subsumption_resolution,[],[f190,f61])).
% 1.82/0.59  fof(f190,plain,(
% 1.82/0.59    v1_funct_1(k2_funct_1(sK4)) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 1.82/0.59    inference(subsumption_resolution,[],[f189,f62])).
% 1.82/0.59  fof(f189,plain,(
% 1.82/0.59    v1_funct_1(k2_funct_1(sK4)) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 1.82/0.59    inference(subsumption_resolution,[],[f188,f63])).
% 1.82/0.59  fof(f188,plain,(
% 1.82/0.59    v1_funct_1(k2_funct_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v3_funct_2(sK4,sK2,sK2) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4)),
% 1.82/0.59    inference(superposition,[],[f160,f78])).
% 1.82/0.59  fof(f160,plain,(
% 1.82/0.59    v1_funct_1(k2_funct_2(sK2,sK4))),
% 1.82/0.59    inference(resolution,[],[f130,f79])).
% 1.82/0.59  fof(f79,plain,(
% 1.82/0.59    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~sP0(X0,X1)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f55])).
% 1.82/0.59  fof(f285,plain,(
% 1.82/0.59    sP1(sK2,k2_funct_1(sK4)) | ~v1_funct_1(k2_funct_1(sK4))),
% 1.82/0.59    inference(subsumption_resolution,[],[f275,f228])).
% 1.82/0.59  fof(f228,plain,(
% 1.82/0.59    v3_funct_2(k2_funct_1(sK4),sK2,sK2)),
% 1.82/0.59    inference(subsumption_resolution,[],[f225,f130])).
% 1.82/0.59  fof(f225,plain,(
% 1.82/0.59    v3_funct_2(k2_funct_1(sK4),sK2,sK2) | ~sP0(sK2,sK4)),
% 1.82/0.59    inference(superposition,[],[f81,f133])).
% 1.82/0.59  fof(f81,plain,(
% 1.82/0.59    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~sP0(X0,X1)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f55])).
% 1.82/0.59  fof(f275,plain,(
% 1.82/0.59    sP1(sK2,k2_funct_1(sK4)) | ~v3_funct_2(k2_funct_1(sK4),sK2,sK2) | ~v1_funct_1(k2_funct_1(sK4))),
% 1.82/0.59    inference(resolution,[],[f229,f93])).
% 1.82/0.59  fof(f454,plain,(
% 1.82/0.59    k2_relat_1(k2_funct_1(sK4)) = k10_relat_1(sK4,k1_relat_1(k2_funct_1(sK4)))),
% 1.82/0.59    inference(subsumption_resolution,[],[f446,f287])).
% 1.82/0.59  fof(f446,plain,(
% 1.82/0.59    k2_relat_1(k2_funct_1(sK4)) = k10_relat_1(sK4,k1_relat_1(k2_funct_1(sK4))) | ~v1_relat_1(k2_funct_1(sK4))),
% 1.82/0.59    inference(superposition,[],[f419,f67])).
% 1.82/0.59  fof(f67,plain,(
% 1.82/0.59    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f24])).
% 1.82/0.59  fof(f24,plain,(
% 1.82/0.59    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.82/0.59    inference(ennf_transformation,[],[f6])).
% 1.82/0.59  fof(f6,axiom,(
% 1.82/0.59    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.82/0.59  fof(f419,plain,(
% 1.82/0.59    ( ! [X6] : (k10_relat_1(sK4,X6) = k9_relat_1(k2_funct_1(sK4),X6)) )),
% 1.82/0.59    inference(subsumption_resolution,[],[f418,f136])).
% 1.82/0.59  fof(f418,plain,(
% 1.82/0.59    ( ! [X6] : (k10_relat_1(sK4,X6) = k9_relat_1(k2_funct_1(sK4),X6) | ~v1_relat_1(sK4)) )),
% 1.82/0.59    inference(subsumption_resolution,[],[f104,f165])).
% 1.82/0.59  fof(f165,plain,(
% 1.82/0.59    v2_funct_1(sK4)),
% 1.82/0.59    inference(resolution,[],[f135,f91])).
% 1.82/0.59  fof(f91,plain,(
% 1.82/0.59    ( ! [X0,X1] : (v2_funct_1(X1) | ~sP1(X0,X1)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f59])).
% 1.82/0.59  fof(f104,plain,(
% 1.82/0.59    ( ! [X6] : (k10_relat_1(sK4,X6) = k9_relat_1(k2_funct_1(sK4),X6) | ~v2_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 1.82/0.59    inference(resolution,[],[f60,f73])).
% 1.82/0.59  fof(f73,plain,(
% 1.82/0.59    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f29])).
% 1.82/0.59  fof(f29,plain,(
% 1.82/0.59    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.82/0.59    inference(flattening,[],[f28])).
% 1.82/0.59  fof(f28,plain,(
% 1.82/0.59    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.82/0.59    inference(ennf_transformation,[],[f10])).
% 1.82/0.59  fof(f10,axiom,(
% 1.82/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 1.82/0.59  fof(f211,plain,(
% 1.82/0.59    k1_relat_1(sK4) = k10_relat_1(sK4,sK2)),
% 1.82/0.59    inference(subsumption_resolution,[],[f205,f136])).
% 1.82/0.59  fof(f205,plain,(
% 1.82/0.59    k1_relat_1(sK4) = k10_relat_1(sK4,sK2) | ~v1_relat_1(sK4)),
% 1.82/0.59    inference(superposition,[],[f66,f177])).
% 1.82/0.59  fof(f66,plain,(
% 1.82/0.59    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f23])).
% 1.82/0.59  fof(f23,plain,(
% 1.82/0.59    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.82/0.59    inference(ennf_transformation,[],[f8])).
% 1.82/0.59  fof(f8,axiom,(
% 1.82/0.59    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.82/0.59  fof(f622,plain,(
% 1.82/0.59    ~r1_tarski(sK3,k1_relat_1(sK4))),
% 1.82/0.59    inference(trivial_inequality_removal,[],[f616])).
% 1.82/0.59  fof(f616,plain,(
% 1.82/0.59    sK3 != sK3 | ~r1_tarski(sK3,k1_relat_1(sK4))),
% 1.82/0.59    inference(backward_demodulation,[],[f360,f539])).
% 1.82/0.59  fof(f539,plain,(
% 1.82/0.59    sK3 = k9_relat_1(sK4,k10_relat_1(sK4,sK3))),
% 1.82/0.59    inference(resolution,[],[f503,f64])).
% 1.82/0.59  fof(f503,plain,(
% 1.82/0.59    ( ! [X5] : (~r1_tarski(X5,sK2) | k9_relat_1(sK4,k10_relat_1(sK4,X5)) = X5) )),
% 1.82/0.59    inference(forward_demodulation,[],[f502,f177])).
% 1.82/0.59  fof(f502,plain,(
% 1.82/0.59    ( ! [X5] : (k9_relat_1(sK4,k10_relat_1(sK4,X5)) = X5 | ~r1_tarski(X5,k2_relat_1(sK4))) )),
% 1.82/0.59    inference(subsumption_resolution,[],[f103,f136])).
% 1.82/0.59  fof(f103,plain,(
% 1.82/0.59    ( ! [X5] : (k9_relat_1(sK4,k10_relat_1(sK4,X5)) = X5 | ~r1_tarski(X5,k2_relat_1(sK4)) | ~v1_relat_1(sK4)) )),
% 1.82/0.59    inference(resolution,[],[f60,f74])).
% 1.82/0.59  fof(f360,plain,(
% 1.82/0.59    ~r1_tarski(sK3,k1_relat_1(sK4)) | sK3 != k9_relat_1(sK4,k10_relat_1(sK4,sK3))),
% 1.82/0.59    inference(forward_demodulation,[],[f359,f122])).
% 1.82/0.59  fof(f122,plain,(
% 1.82/0.59    ( ! [X0] : (k7_relset_1(sK2,sK2,sK4,X0) = k9_relat_1(sK4,X0)) )),
% 1.82/0.59    inference(resolution,[],[f63,f95])).
% 1.82/0.59  fof(f95,plain,(
% 1.82/0.59    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.82/0.59    inference(cnf_transformation,[],[f46])).
% 1.82/0.59  fof(f46,plain,(
% 1.82/0.59    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.59    inference(ennf_transformation,[],[f13])).
% 1.82/0.59  fof(f13,axiom,(
% 1.82/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.82/0.59  fof(f359,plain,(
% 1.82/0.59    sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3)) | ~r1_tarski(sK3,k1_relat_1(sK4))),
% 1.82/0.59    inference(subsumption_resolution,[],[f358,f136])).
% 1.82/0.59  fof(f358,plain,(
% 1.82/0.59    sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3)) | ~r1_tarski(sK3,k1_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 1.82/0.59    inference(subsumption_resolution,[],[f357,f60])).
% 1.82/0.59  fof(f357,plain,(
% 1.82/0.59    sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3)) | ~r1_tarski(sK3,k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.82/0.59    inference(subsumption_resolution,[],[f353,f165])).
% 1.82/0.59  fof(f353,plain,(
% 1.82/0.59    sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3)) | ~v2_funct_1(sK4) | ~r1_tarski(sK3,k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.82/0.59    inference(trivial_inequality_removal,[],[f352])).
% 1.82/0.59  fof(f352,plain,(
% 1.82/0.59    sK3 != sK3 | sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3)) | ~v2_funct_1(sK4) | ~r1_tarski(sK3,k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 1.82/0.59    inference(superposition,[],[f326,f75])).
% 1.82/0.59  fof(f75,plain,(
% 1.82/0.59    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.82/0.59    inference(cnf_transformation,[],[f33])).
% 1.82/0.59  fof(f33,plain,(
% 1.82/0.59    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.82/0.59    inference(flattening,[],[f32])).
% 1.82/0.59  fof(f32,plain,(
% 1.82/0.59    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.82/0.59    inference(ennf_transformation,[],[f11])).
% 1.82/0.59  fof(f11,axiom,(
% 1.82/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 1.82/0.59  fof(f326,plain,(
% 1.82/0.59    sK3 != k10_relat_1(sK4,k9_relat_1(sK4,sK3)) | sK3 != k7_relset_1(sK2,sK2,sK4,k10_relat_1(sK4,sK3))),
% 1.82/0.59    inference(forward_demodulation,[],[f325,f123])).
% 1.82/0.59  fof(f123,plain,(
% 1.82/0.59    ( ! [X1] : (k8_relset_1(sK2,sK2,sK4,X1) = k10_relat_1(sK4,X1)) )),
% 1.82/0.59    inference(resolution,[],[f63,f94])).
% 1.82/0.59  fof(f94,plain,(
% 1.82/0.59    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.82/0.59    inference(cnf_transformation,[],[f45])).
% 1.82/0.59  fof(f45,plain,(
% 1.82/0.59    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.59    inference(ennf_transformation,[],[f14])).
% 1.82/0.59  fof(f14,axiom,(
% 1.82/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.82/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.82/0.59  fof(f325,plain,(
% 1.82/0.59    sK3 != k10_relat_1(sK4,k9_relat_1(sK4,sK3)) | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3))),
% 1.82/0.59    inference(backward_demodulation,[],[f270,f123])).
% 1.82/0.59  fof(f270,plain,(
% 1.82/0.59    sK3 != k8_relset_1(sK2,sK2,sK4,k9_relat_1(sK4,sK3)) | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3))),
% 1.82/0.59    inference(backward_demodulation,[],[f65,f122])).
% 1.82/0.59  fof(f65,plain,(
% 1.82/0.59    sK3 != k8_relset_1(sK2,sK2,sK4,k7_relset_1(sK2,sK2,sK4,sK3)) | sK3 != k7_relset_1(sK2,sK2,sK4,k8_relset_1(sK2,sK2,sK4,sK3))),
% 1.82/0.59    inference(cnf_transformation,[],[f52])).
% 1.82/0.59  % SZS output end Proof for theBenchmark
% 1.82/0.59  % (28055)------------------------------
% 1.82/0.59  % (28055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.59  % (28055)Termination reason: Refutation
% 1.82/0.59  
% 1.82/0.59  % (28055)Memory used [KB]: 1918
% 1.82/0.59  % (28055)Time elapsed: 0.132 s
% 1.82/0.59  % (28055)------------------------------
% 1.82/0.59  % (28055)------------------------------
% 1.82/0.59  % (28069)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.82/0.59  % (28046)Success in time 0.236 s
%------------------------------------------------------------------------------

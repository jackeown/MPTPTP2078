%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:57 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 115 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  198 ( 312 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f76,f91,f94])).

fof(f94,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f92,f36])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

fof(f92,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl5_3 ),
    inference(resolution,[],[f70,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(condensation,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f70,plain,
    ( ~ r2_relset_1(sK1,sK0,sK3,sK3)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_3
  <=> r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f91,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f88,f37])).

fof(f37,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_2 ),
    inference(resolution,[],[f86,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f86,plain,
    ( ! [X0] : ~ r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,X0))
    | spl5_2 ),
    inference(resolution,[],[f84,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f84,plain,
    ( ! [X0] : ~ r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | spl5_2 ),
    inference(resolution,[],[f83,f36])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) )
    | spl5_2 ),
    inference(resolution,[],[f82,f39])).

fof(f39,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f82,plain,
    ( ! [X4,X3] :
        ( v1_xboole_0(X3)
        | ~ r1_tarski(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X4)))
        | ~ m1_subset_1(sK3,X3) )
    | spl5_2 ),
    inference(resolution,[],[f79,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3,X0)
        | ~ r1_tarski(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) )
    | spl5_2 ),
    inference(resolution,[],[f78,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f78,plain,
    ( ! [X0] : ~ r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | spl5_2 ),
    inference(resolution,[],[f77,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f77,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | spl5_2 ),
    inference(resolution,[],[f66,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f66,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl5_2
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f76,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f73,f41])).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f73,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl5_1 ),
    inference(resolution,[],[f72,f36])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl5_1 ),
    inference(resolution,[],[f62,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f62,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f71,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f58,f68,f64,f60])).

fof(f58,plain,
    ( ~ r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f57,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f57,plain,(
    ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) ),
    inference(subsumption_resolution,[],[f56,f36])).

fof(f56,plain,
    ( ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f38,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

% (4787)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f38,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:14:26 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.52  % (4791)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.52  % (4795)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.52  % (4815)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.23/0.52  % (4806)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.53  % (4806)Refutation not found, incomplete strategy% (4806)------------------------------
% 0.23/0.53  % (4806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (4788)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.54  % (4788)Refutation not found, incomplete strategy% (4788)------------------------------
% 0.23/0.54  % (4788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (4788)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (4788)Memory used [KB]: 10746
% 0.23/0.54  % (4788)Time elapsed: 0.114 s
% 0.23/0.54  % (4788)------------------------------
% 0.23/0.54  % (4788)------------------------------
% 0.23/0.54  % (4806)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (4806)Memory used [KB]: 10746
% 0.23/0.54  % (4806)Time elapsed: 0.107 s
% 0.23/0.54  % (4806)------------------------------
% 0.23/0.54  % (4806)------------------------------
% 0.23/0.54  % (4789)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.54  % (4802)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.54  % (4792)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.54  % (4789)Refutation found. Thanks to Tanya!
% 0.23/0.54  % SZS status Theorem for theBenchmark
% 0.23/0.54  % SZS output start Proof for theBenchmark
% 0.23/0.54  fof(f95,plain,(
% 0.23/0.54    $false),
% 0.23/0.54    inference(avatar_sat_refutation,[],[f71,f76,f91,f94])).
% 0.23/0.54  fof(f94,plain,(
% 0.23/0.54    spl5_3),
% 0.23/0.54    inference(avatar_contradiction_clause,[],[f93])).
% 0.23/0.54  fof(f93,plain,(
% 0.23/0.54    $false | spl5_3),
% 0.23/0.54    inference(subsumption_resolution,[],[f92,f36])).
% 0.23/0.54  fof(f36,plain,(
% 0.23/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.23/0.54    inference(cnf_transformation,[],[f31])).
% 0.23/0.54  fof(f31,plain,(
% 0.23/0.54    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f30])).
% 0.23/0.54  fof(f30,plain,(
% 0.23/0.54    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f16,plain,(
% 0.23/0.54    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.23/0.54    inference(flattening,[],[f15])).
% 0.23/0.54  fof(f15,plain,(
% 0.23/0.54    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.23/0.54    inference(ennf_transformation,[],[f14])).
% 0.23/0.54  fof(f14,negated_conjecture,(
% 0.23/0.54    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.23/0.54    inference(negated_conjecture,[],[f13])).
% 0.23/0.54  fof(f13,conjecture,(
% 0.23/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).
% 0.23/0.54  fof(f92,plain,(
% 0.23/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl5_3),
% 0.23/0.54    inference(resolution,[],[f70,f55])).
% 0.23/0.54  fof(f55,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.54    inference(condensation,[],[f54])).
% 0.23/0.54  fof(f54,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f29])).
% 0.23/0.54  fof(f29,plain,(
% 0.23/0.54    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.54    inference(flattening,[],[f28])).
% 0.23/0.54  fof(f28,plain,(
% 0.23/0.54    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.23/0.54    inference(ennf_transformation,[],[f12])).
% 0.23/0.54  fof(f12,axiom,(
% 0.23/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.23/0.54  fof(f70,plain,(
% 0.23/0.54    ~r2_relset_1(sK1,sK0,sK3,sK3) | spl5_3),
% 0.23/0.54    inference(avatar_component_clause,[],[f68])).
% 0.23/0.54  fof(f68,plain,(
% 0.23/0.54    spl5_3 <=> r2_relset_1(sK1,sK0,sK3,sK3)),
% 0.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.23/0.54  fof(f91,plain,(
% 0.23/0.54    spl5_2),
% 0.23/0.54    inference(avatar_contradiction_clause,[],[f90])).
% 0.23/0.54  fof(f90,plain,(
% 0.23/0.54    $false | spl5_2),
% 0.23/0.54    inference(subsumption_resolution,[],[f88,f37])).
% 0.23/0.54  fof(f37,plain,(
% 0.23/0.54    r1_tarski(sK1,sK2)),
% 0.23/0.54    inference(cnf_transformation,[],[f31])).
% 0.23/0.54  fof(f88,plain,(
% 0.23/0.54    ~r1_tarski(sK1,sK2) | spl5_2),
% 0.23/0.54    inference(resolution,[],[f86,f49])).
% 0.23/0.54  fof(f49,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f25])).
% 0.23/0.54  fof(f25,plain,(
% 0.23/0.54    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.23/0.54    inference(ennf_transformation,[],[f2])).
% 0.23/0.54  fof(f2,axiom,(
% 0.23/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.23/0.54  fof(f86,plain,(
% 0.23/0.54    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,X0))) ) | spl5_2),
% 0.23/0.54    inference(resolution,[],[f84,f44])).
% 0.23/0.54  fof(f44,plain,(
% 0.23/0.54    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f21])).
% 0.23/0.54  fof(f21,plain,(
% 0.23/0.54    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.23/0.54    inference(ennf_transformation,[],[f3])).
% 0.23/0.54  fof(f3,axiom,(
% 0.23/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.23/0.54  fof(f84,plain,(
% 0.23/0.54    ( ! [X0] : (~r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | spl5_2),
% 0.23/0.54    inference(resolution,[],[f83,f36])).
% 0.23/0.54  fof(f83,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))) ) | spl5_2),
% 0.23/0.54    inference(resolution,[],[f82,f39])).
% 0.23/0.54  fof(f39,plain,(
% 0.23/0.54    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f4])).
% 0.23/0.54  fof(f4,axiom,(
% 0.23/0.54    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.23/0.54  fof(f82,plain,(
% 0.23/0.54    ( ! [X4,X3] : (v1_xboole_0(X3) | ~r1_tarski(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | ~m1_subset_1(sK3,X3)) ) | spl5_2),
% 0.23/0.54    inference(resolution,[],[f79,f43])).
% 0.23/0.54  fof(f43,plain,(
% 0.23/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f20])).
% 0.23/0.54  fof(f20,plain,(
% 0.23/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.23/0.54    inference(flattening,[],[f19])).
% 0.23/0.54  fof(f19,plain,(
% 0.23/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.23/0.54    inference(ennf_transformation,[],[f6])).
% 0.23/0.54  fof(f6,axiom,(
% 0.23/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.23/0.54  fof(f79,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~r2_hidden(sK3,X0) | ~r1_tarski(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))) ) | spl5_2),
% 0.23/0.54    inference(resolution,[],[f78,f46])).
% 0.23/0.54  fof(f46,plain,(
% 0.23/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f35])).
% 0.23/0.54  fof(f35,plain,(
% 0.23/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 0.23/0.54  fof(f34,plain,(
% 0.23/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f33,plain,(
% 0.23/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.54    inference(rectify,[],[f32])).
% 0.23/0.54  fof(f32,plain,(
% 0.23/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.54    inference(nnf_transformation,[],[f24])).
% 0.23/0.54  fof(f24,plain,(
% 0.23/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.23/0.54    inference(ennf_transformation,[],[f1])).
% 0.23/0.54  fof(f1,axiom,(
% 0.23/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.23/0.54  fof(f78,plain,(
% 0.23/0.54    ( ! [X0] : (~r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | spl5_2),
% 0.23/0.54    inference(resolution,[],[f77,f42])).
% 0.23/0.54  fof(f42,plain,(
% 0.23/0.54    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f18])).
% 0.23/0.54  fof(f18,plain,(
% 0.23/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.23/0.54    inference(ennf_transformation,[],[f5])).
% 0.23/0.54  fof(f5,axiom,(
% 0.23/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.23/0.54  fof(f77,plain,(
% 0.23/0.54    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | spl5_2),
% 0.23/0.54    inference(resolution,[],[f66,f51])).
% 0.23/0.54  fof(f51,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f26])).
% 0.23/0.54  fof(f26,plain,(
% 0.23/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.54    inference(ennf_transformation,[],[f10])).
% 0.23/0.54  fof(f10,axiom,(
% 0.23/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.23/0.54  fof(f66,plain,(
% 0.23/0.54    ~v4_relat_1(sK3,sK2) | spl5_2),
% 0.23/0.54    inference(avatar_component_clause,[],[f64])).
% 0.23/0.54  fof(f64,plain,(
% 0.23/0.54    spl5_2 <=> v4_relat_1(sK3,sK2)),
% 0.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.23/0.54  fof(f76,plain,(
% 0.23/0.54    spl5_1),
% 0.23/0.54    inference(avatar_contradiction_clause,[],[f75])).
% 0.23/0.54  fof(f75,plain,(
% 0.23/0.54    $false | spl5_1),
% 0.23/0.54    inference(subsumption_resolution,[],[f73,f41])).
% 0.23/0.54  fof(f41,plain,(
% 0.23/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f8])).
% 0.23/0.54  fof(f8,axiom,(
% 0.23/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.23/0.54  fof(f73,plain,(
% 0.23/0.54    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl5_1),
% 0.23/0.54    inference(resolution,[],[f72,f36])).
% 0.23/0.54  fof(f72,plain,(
% 0.23/0.54    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl5_1),
% 0.23/0.54    inference(resolution,[],[f62,f40])).
% 0.23/0.54  fof(f40,plain,(
% 0.23/0.54    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f17])).
% 0.23/0.54  fof(f17,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.23/0.54    inference(ennf_transformation,[],[f7])).
% 0.23/0.54  fof(f7,axiom,(
% 0.23/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.23/0.54  fof(f62,plain,(
% 0.23/0.54    ~v1_relat_1(sK3) | spl5_1),
% 0.23/0.54    inference(avatar_component_clause,[],[f60])).
% 0.23/0.54  fof(f60,plain,(
% 0.23/0.54    spl5_1 <=> v1_relat_1(sK3)),
% 0.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.23/0.54  fof(f71,plain,(
% 0.23/0.54    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.23/0.54    inference(avatar_split_clause,[],[f58,f68,f64,f60])).
% 0.23/0.54  fof(f58,plain,(
% 0.23/0.54    ~r2_relset_1(sK1,sK0,sK3,sK3) | ~v4_relat_1(sK3,sK2) | ~v1_relat_1(sK3)),
% 0.23/0.54    inference(superposition,[],[f57,f45])).
% 0.23/0.54  fof(f45,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f23])).
% 0.23/0.54  fof(f23,plain,(
% 0.23/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.23/0.54    inference(flattening,[],[f22])).
% 0.23/0.54  fof(f22,plain,(
% 0.23/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.23/0.54    inference(ennf_transformation,[],[f9])).
% 0.23/0.54  fof(f9,axiom,(
% 0.23/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.23/0.54  fof(f57,plain,(
% 0.23/0.54    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)),
% 0.23/0.54    inference(subsumption_resolution,[],[f56,f36])).
% 0.23/0.54  fof(f56,plain,(
% 0.23/0.54    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.23/0.54    inference(superposition,[],[f38,f53])).
% 0.23/0.54  fof(f53,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f27])).
% 0.23/0.54  % (4787)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.54  fof(f27,plain,(
% 0.23/0.54    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.54    inference(ennf_transformation,[],[f11])).
% 0.23/0.54  fof(f11,axiom,(
% 0.23/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.23/0.54  fof(f38,plain,(
% 0.23/0.54    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.23/0.54    inference(cnf_transformation,[],[f31])).
% 0.23/0.54  % SZS output end Proof for theBenchmark
% 0.23/0.54  % (4789)------------------------------
% 0.23/0.54  % (4789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (4789)Termination reason: Refutation
% 0.23/0.54  
% 0.23/0.54  % (4789)Memory used [KB]: 10746
% 0.23/0.54  % (4789)Time elapsed: 0.125 s
% 0.23/0.54  % (4789)------------------------------
% 0.23/0.54  % (4789)------------------------------
% 0.23/0.54  % (4785)Success in time 0.172 s
%------------------------------------------------------------------------------

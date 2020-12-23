%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:55 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 257 expanded)
%              Number of leaves         :   18 (  76 expanded)
%              Depth                    :   22
%              Number of atoms          :  254 ( 666 expanded)
%              Number of equality atoms :  110 ( 303 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(subsumption_resolution,[],[f174,f53])).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f174,plain,(
    ~ r1_tarski(k1_xboole_0,sK3) ),
    inference(superposition,[],[f124,f143])).

fof(f143,plain,(
    k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(subsumption_resolution,[],[f141,f52])).

fof(f52,plain,(
    sK3 != k1_funct_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( sK3 != k1_funct_1(sK5,sK4)
    & r2_hidden(sK4,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK5,sK2,k1_tarski(sK3))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f20,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK3 != k1_funct_1(sK5,sK4)
      & r2_hidden(sK4,sK2)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      & v1_funct_2(sK5,sK2,k1_tarski(sK3))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f141,plain,
    ( k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | sK3 = k1_funct_1(sK5,sK4) ),
    inference(resolution,[],[f137,f106])).

fof(f106,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f57,f97])).

fof(f97,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f96])).

fof(f96,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f73,f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f74,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f75,f76])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

% (23742)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f137,plain,
    ( r2_hidden(k1_funct_1(sK5,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(resolution,[],[f136,f51])).

fof(f51,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f136,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
      | r2_hidden(k1_funct_1(sK5,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ) ),
    inference(resolution,[],[f135,f122])).

fof(f122,plain,(
    v5_relat_1(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(resolution,[],[f98,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f98,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(definition_unfolding,[],[f50,f97])).

fof(f50,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK5,X0)
      | ~ r2_hidden(X1,sK2)
      | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
      | r2_hidden(k1_funct_1(sK5,X1),X0) ) ),
    inference(resolution,[],[f133,f98])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v5_relat_1(sK5,X1)
      | ~ r2_hidden(X0,sK2)
      | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
      | r2_hidden(k1_funct_1(sK5,X0),X1) ) ),
    inference(resolution,[],[f132,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK5)
      | r2_hidden(k1_funct_1(sK5,X0),X1)
      | ~ v5_relat_1(sK5,X1)
      | ~ r2_hidden(X0,sK2)
      | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ) ),
    inference(subsumption_resolution,[],[f131,f48])).

fof(f48,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(k1_funct_1(sK5,X0),X1)
      | ~ v1_funct_1(sK5)
      | ~ v5_relat_1(sK5,X1)
      | ~ v1_relat_1(sK5)
      | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ) ),
    inference(superposition,[],[f56,f130])).

fof(f130,plain,
    ( sK2 = k1_relat_1(sK5)
    | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(subsumption_resolution,[],[f128,f98])).

fof(f128,plain,
    ( sK2 = k1_relat_1(sK5)
    | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(superposition,[],[f127,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f127,plain,
    ( sK2 = k1_relset_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5)
    | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(subsumption_resolution,[],[f126,f99])).

fof(f99,plain,(
    v1_funct_2(sK5,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f49,f97])).

fof(f49,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f126,plain,
    ( ~ v1_funct_2(sK5,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | sK2 = k1_relset_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) ),
    inference(resolution,[],[f67,f98])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f124,plain,(
    ! [X0] : ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0) ),
    inference(resolution,[],[f105,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f105,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f58,f97])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:31:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.19/0.52  % (23745)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.19/0.52  % (23748)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.19/0.52  % (23756)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.19/0.52  % (23746)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.19/0.52  % (23738)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.19/0.52  % (23756)Refutation found. Thanks to Tanya!
% 1.19/0.52  % SZS status Theorem for theBenchmark
% 1.19/0.53  % (23750)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.19/0.53  % (23758)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.19/0.53  % (23740)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.19/0.53  % (23737)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.19/0.53  % (23750)Refutation not found, incomplete strategy% (23750)------------------------------
% 1.19/0.53  % (23750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.53  % (23750)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.53  
% 1.19/0.53  % (23750)Memory used [KB]: 10746
% 1.19/0.53  % (23750)Time elapsed: 0.113 s
% 1.19/0.53  % (23750)------------------------------
% 1.19/0.53  % (23750)------------------------------
% 1.19/0.53  % SZS output start Proof for theBenchmark
% 1.19/0.53  fof(f177,plain,(
% 1.19/0.53    $false),
% 1.19/0.53    inference(subsumption_resolution,[],[f174,f53])).
% 1.19/0.53  fof(f53,plain,(
% 1.19/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f1])).
% 1.19/0.53  fof(f1,axiom,(
% 1.19/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.19/0.53  fof(f174,plain,(
% 1.19/0.53    ~r1_tarski(k1_xboole_0,sK3)),
% 1.19/0.53    inference(superposition,[],[f124,f143])).
% 1.19/0.53  fof(f143,plain,(
% 1.19/0.53    k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 1.19/0.53    inference(subsumption_resolution,[],[f141,f52])).
% 1.19/0.53  fof(f52,plain,(
% 1.19/0.53    sK3 != k1_funct_1(sK5,sK4)),
% 1.19/0.53    inference(cnf_transformation,[],[f34])).
% 1.19/0.53  fof(f34,plain,(
% 1.19/0.53    sK3 != k1_funct_1(sK5,sK4) & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5)),
% 1.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f20,f33])).
% 1.19/0.53  fof(f33,plain,(
% 1.19/0.53    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK3 != k1_funct_1(sK5,sK4) & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5))),
% 1.19/0.53    introduced(choice_axiom,[])).
% 1.19/0.53  fof(f20,plain,(
% 1.19/0.53    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.19/0.53    inference(flattening,[],[f19])).
% 1.19/0.53  fof(f19,plain,(
% 1.19/0.53    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.19/0.53    inference(ennf_transformation,[],[f18])).
% 1.19/0.53  fof(f18,negated_conjecture,(
% 1.19/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.19/0.53    inference(negated_conjecture,[],[f17])).
% 1.19/0.53  fof(f17,conjecture,(
% 1.19/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 1.19/0.53  fof(f141,plain,(
% 1.19/0.53    k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | sK3 = k1_funct_1(sK5,sK4)),
% 1.19/0.53    inference(resolution,[],[f137,f106])).
% 1.19/0.53  fof(f106,plain,(
% 1.19/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.19/0.53    inference(equality_resolution,[],[f103])).
% 1.19/0.53  fof(f103,plain,(
% 1.19/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.19/0.53    inference(definition_unfolding,[],[f57,f97])).
% 1.19/0.53  fof(f97,plain,(
% 1.19/0.53    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.19/0.53    inference(definition_unfolding,[],[f54,f96])).
% 1.19/0.53  fof(f96,plain,(
% 1.19/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.19/0.53    inference(definition_unfolding,[],[f55,f95])).
% 1.19/0.53  fof(f95,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.19/0.53    inference(definition_unfolding,[],[f62,f94])).
% 1.19/0.53  fof(f94,plain,(
% 1.19/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.19/0.53    inference(definition_unfolding,[],[f73,f93])).
% 1.19/0.53  fof(f93,plain,(
% 1.19/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.19/0.53    inference(definition_unfolding,[],[f74,f92])).
% 1.19/0.53  fof(f92,plain,(
% 1.19/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.19/0.53    inference(definition_unfolding,[],[f75,f76])).
% 1.19/0.53  fof(f76,plain,(
% 1.19/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f9])).
% 1.19/0.53  fof(f9,axiom,(
% 1.19/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.19/0.53  fof(f75,plain,(
% 1.19/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f8])).
% 1.19/0.53  fof(f8,axiom,(
% 1.19/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.19/0.53  fof(f74,plain,(
% 1.19/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f7])).
% 1.19/0.53  fof(f7,axiom,(
% 1.19/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.19/0.53  fof(f73,plain,(
% 1.19/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f6])).
% 1.19/0.53  fof(f6,axiom,(
% 1.19/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.19/0.53  fof(f62,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f5])).
% 1.19/0.53  fof(f5,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.19/0.53  fof(f55,plain,(
% 1.19/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f4])).
% 1.19/0.53  fof(f4,axiom,(
% 1.19/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.19/0.53  % (23742)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.19/0.53  fof(f54,plain,(
% 1.19/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f3])).
% 1.19/0.53  fof(f3,axiom,(
% 1.19/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.19/0.53  fof(f57,plain,(
% 1.19/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.19/0.53    inference(cnf_transformation,[],[f38])).
% 1.19/0.53  fof(f38,plain,(
% 1.19/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).
% 1.19/0.53  fof(f37,plain,(
% 1.19/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 1.19/0.53    introduced(choice_axiom,[])).
% 1.19/0.53  fof(f36,plain,(
% 1.19/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.19/0.53    inference(rectify,[],[f35])).
% 1.19/0.53  fof(f35,plain,(
% 1.19/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.19/0.53    inference(nnf_transformation,[],[f2])).
% 1.19/0.53  fof(f2,axiom,(
% 1.19/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.19/0.53  fof(f137,plain,(
% 1.19/0.53    r2_hidden(k1_funct_1(sK5,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 1.19/0.53    inference(resolution,[],[f136,f51])).
% 1.19/0.53  fof(f51,plain,(
% 1.19/0.53    r2_hidden(sK4,sK2)),
% 1.19/0.53    inference(cnf_transformation,[],[f34])).
% 1.19/0.53  fof(f136,plain,(
% 1.19/0.53    ( ! [X0] : (~r2_hidden(X0,sK2) | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | r2_hidden(k1_funct_1(sK5,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) )),
% 1.19/0.53    inference(resolution,[],[f135,f122])).
% 1.19/0.53  fof(f122,plain,(
% 1.19/0.53    v5_relat_1(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),
% 1.19/0.53    inference(resolution,[],[f98,f66])).
% 1.19/0.53  fof(f66,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f26])).
% 1.19/0.53  fof(f26,plain,(
% 1.19/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(ennf_transformation,[],[f14])).
% 1.19/0.53  fof(f14,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.19/0.53  fof(f98,plain,(
% 1.19/0.53    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))),
% 1.19/0.53    inference(definition_unfolding,[],[f50,f97])).
% 1.19/0.53  fof(f50,plain,(
% 1.19/0.53    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 1.19/0.53    inference(cnf_transformation,[],[f34])).
% 1.19/0.53  fof(f135,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~v5_relat_1(sK5,X0) | ~r2_hidden(X1,sK2) | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | r2_hidden(k1_funct_1(sK5,X1),X0)) )),
% 1.19/0.53    inference(resolution,[],[f133,f98])).
% 1.19/0.53  fof(f133,plain,(
% 1.19/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v5_relat_1(sK5,X1) | ~r2_hidden(X0,sK2) | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | r2_hidden(k1_funct_1(sK5,X0),X1)) )),
% 1.19/0.53    inference(resolution,[],[f132,f63])).
% 1.19/0.53  fof(f63,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/0.53    inference(cnf_transformation,[],[f24])).
% 1.19/0.53  fof(f24,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(ennf_transformation,[],[f13])).
% 1.19/0.53  fof(f13,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.19/0.53  fof(f132,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~v1_relat_1(sK5) | r2_hidden(k1_funct_1(sK5,X0),X1) | ~v5_relat_1(sK5,X1) | ~r2_hidden(X0,sK2) | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) )),
% 1.19/0.53    inference(subsumption_resolution,[],[f131,f48])).
% 1.19/0.53  fof(f48,plain,(
% 1.19/0.53    v1_funct_1(sK5)),
% 1.19/0.53    inference(cnf_transformation,[],[f34])).
% 1.19/0.53  fof(f131,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~r2_hidden(X0,sK2) | r2_hidden(k1_funct_1(sK5,X0),X1) | ~v1_funct_1(sK5) | ~v5_relat_1(sK5,X1) | ~v1_relat_1(sK5) | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) )),
% 1.19/0.53    inference(superposition,[],[f56,f130])).
% 1.19/0.53  fof(f130,plain,(
% 1.19/0.53    sK2 = k1_relat_1(sK5) | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 1.19/0.53    inference(subsumption_resolution,[],[f128,f98])).
% 1.19/0.53  fof(f128,plain,(
% 1.19/0.53    sK2 = k1_relat_1(sK5) | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))),
% 1.19/0.53    inference(superposition,[],[f127,f64])).
% 1.19/0.53  fof(f64,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/0.53    inference(cnf_transformation,[],[f25])).
% 1.19/0.53  fof(f25,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(ennf_transformation,[],[f15])).
% 1.19/0.53  fof(f15,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.19/0.53  fof(f127,plain,(
% 1.19/0.53    sK2 = k1_relset_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 1.19/0.53    inference(subsumption_resolution,[],[f126,f99])).
% 1.19/0.53  fof(f99,plain,(
% 1.19/0.53    v1_funct_2(sK5,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),
% 1.19/0.53    inference(definition_unfolding,[],[f49,f97])).
% 1.19/0.53  fof(f49,plain,(
% 1.19/0.53    v1_funct_2(sK5,sK2,k1_tarski(sK3))),
% 1.19/0.53    inference(cnf_transformation,[],[f34])).
% 1.19/0.53  fof(f126,plain,(
% 1.19/0.53    ~v1_funct_2(sK5,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | sK2 = k1_relset_1(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5)),
% 1.19/0.53    inference(resolution,[],[f67,f98])).
% 1.19/0.53  fof(f67,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.19/0.53    inference(cnf_transformation,[],[f39])).
% 1.19/0.53  fof(f39,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(nnf_transformation,[],[f28])).
% 1.19/0.53  fof(f28,plain,(
% 1.19/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(flattening,[],[f27])).
% 1.19/0.53  fof(f27,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(ennf_transformation,[],[f16])).
% 1.19/0.53  fof(f16,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.19/0.53  fof(f56,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X2),X0) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f22])).
% 1.19/0.53  fof(f22,plain,(
% 1.19/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.19/0.53    inference(flattening,[],[f21])).
% 1.19/0.53  fof(f21,plain,(
% 1.19/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.19/0.53    inference(ennf_transformation,[],[f11])).
% 1.19/0.53  fof(f11,axiom,(
% 1.19/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 1.19/0.53  fof(f124,plain,(
% 1.19/0.53    ( ! [X0] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X0)) )),
% 1.19/0.53    inference(resolution,[],[f105,f61])).
% 1.19/0.53  fof(f61,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f23])).
% 1.19/0.53  fof(f23,plain,(
% 1.19/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.19/0.53    inference(ennf_transformation,[],[f12])).
% 1.19/0.53  fof(f12,axiom,(
% 1.19/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.19/0.53  fof(f105,plain,(
% 1.19/0.53    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 1.19/0.53    inference(equality_resolution,[],[f104])).
% 1.19/0.53  fof(f104,plain,(
% 1.19/0.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 1.19/0.53    inference(equality_resolution,[],[f102])).
% 1.19/0.53  fof(f102,plain,(
% 1.19/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.19/0.53    inference(definition_unfolding,[],[f58,f97])).
% 1.19/0.53  fof(f58,plain,(
% 1.19/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.19/0.53    inference(cnf_transformation,[],[f38])).
% 1.19/0.53  % SZS output end Proof for theBenchmark
% 1.19/0.53  % (23756)------------------------------
% 1.19/0.53  % (23756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.53  % (23756)Termination reason: Refutation
% 1.19/0.53  
% 1.19/0.53  % (23756)Memory used [KB]: 6268
% 1.19/0.53  % (23756)Time elapsed: 0.068 s
% 1.19/0.53  % (23756)------------------------------
% 1.19/0.53  % (23756)------------------------------
% 1.19/0.53  % (23733)Success in time 0.169 s
%------------------------------------------------------------------------------

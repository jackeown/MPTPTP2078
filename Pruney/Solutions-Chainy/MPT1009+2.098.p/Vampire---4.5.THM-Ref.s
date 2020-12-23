%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 326 expanded)
%              Number of leaves         :   20 (  99 expanded)
%              Depth                    :   18
%              Number of atoms          :  276 ( 763 expanded)
%              Number of equality atoms :   86 ( 308 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f94,f155,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
      | ~ sP0(X0) ) ),
    inference(subsumption_resolution,[],[f116,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
      | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ sP0(X0) ) ),
    inference(subsumption_resolution,[],[f114,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
      | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f106,f52])).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(k9_relat_1(X2,X3),X1)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f105])).

% (12833)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X2,X3),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f69,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

% (12821)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_2)).

fof(f155,plain,(
    ~ r1_tarski(k9_relat_1(sK7,sK6),k2_relat_1(sK7)) ),
    inference(subsumption_resolution,[],[f153,f47])).

fof(f47,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK4),sK5,sK7,sK6),k1_tarski(k1_funct_1(sK7,sK4)))
    & k1_xboole_0 != sK5
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5)))
    & v1_funct_2(sK7,k1_tarski(sK4),sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f18,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK4),sK5,sK7,sK6),k1_tarski(k1_funct_1(sK7,sK4)))
      & k1_xboole_0 != sK5
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5)))
      & v1_funct_2(sK7,k1_tarski(sK4),sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f153,plain,
    ( ~ r1_tarski(k9_relat_1(sK7,sK6),k2_relat_1(sK7))
    | k1_xboole_0 = sK5 ),
    inference(resolution,[],[f149,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f149,plain,
    ( sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
    | ~ r1_tarski(k9_relat_1(sK7,sK6),k2_relat_1(sK7)) ),
    inference(superposition,[],[f108,f141])).

fof(f141,plain,
    ( k6_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)) = k2_relat_1(sK7)
    | sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) ),
    inference(subsumption_resolution,[],[f140,f93])).

fof(f93,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f80,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f80,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5))) ),
    inference(definition_unfolding,[],[f46,f78])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f67,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

% (12827)Termination reason: Refutation not found, incomplete strategy
fof(f46,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5))) ),
    inference(cnf_transformation,[],[f37])).

% (12827)Memory used [KB]: 10618
fof(f140,plain,
    ( k6_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)) = k2_relat_1(sK7)
    | ~ v1_relat_1(sK7)
    | sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) ),
    inference(subsumption_resolution,[],[f139,f44])).

% (12827)Time elapsed: 0.143 s
% (12827)------------------------------
% (12827)------------------------------
fof(f44,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f37])).

fof(f139,plain,
    ( k6_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)) = k2_relat_1(sK7)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_relat_1(sK7)
      | k2_relat_1(X0) = k6_enumset1(k1_funct_1(X0,sK4),k1_funct_1(X0,sK4),k1_funct_1(X0,sK4),k1_funct_1(X0,sK4),k1_funct_1(X0,sK4),k1_funct_1(X0,sK4),k1_funct_1(X0,sK4),k1_funct_1(X0,sK4))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) ) ),
    inference(superposition,[],[f82,f111])).

fof(f111,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_relat_1(sK7)
    | sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) ),
    inference(subsumption_resolution,[],[f110,f81])).

fof(f81,plain,(
    v1_funct_2(sK7,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) ),
    inference(definition_unfolding,[],[f45,f78])).

fof(f45,plain,(
    v1_funct_2(sK7,k1_tarski(sK4),sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f110,plain,
    ( ~ v1_funct_2(sK7,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
    | sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_relat_1(sK7) ),
    inference(resolution,[],[f97,f80])).

fof(f97,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f95,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f26,f34,f33,f32])).

fof(f33,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

% (12832)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f95,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | ~ sP2(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f61,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | k2_relat_1(X1) = k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f55,f78,f78])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f108,plain,(
    ~ r1_tarski(k9_relat_1(sK7,sK6),k6_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4))) ),
    inference(subsumption_resolution,[],[f107,f80])).

fof(f107,plain,
    ( ~ r1_tarski(k9_relat_1(sK7,sK6),k6_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5))) ),
    inference(superposition,[],[f79,f68])).

fof(f79,plain,(
    ~ r1_tarski(k7_relset_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5,sK7,sK6),k6_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4))) ),
    inference(definition_unfolding,[],[f48,f78,f78])).

fof(f48,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK4),sK5,sK7,sK6),k1_tarski(k1_funct_1(sK7,sK4))) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    sP0(sK7) ),
    inference(resolution,[],[f93,f87])).

fof(f87,plain,
    ( ~ v1_relat_1(sK7)
    | sP0(sK7) ),
    inference(resolution,[],[f53,f44])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sP0(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f20,f30])).

fof(f20,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:26:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (12818)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (12814)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (12816)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (12824)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (12815)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (12829)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (12828)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (12840)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (12836)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (12823)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (12830)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (12846)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (12814)Refutation not found, incomplete strategy% (12814)------------------------------
% 0.22/0.54  % (12814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12814)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12814)Memory used [KB]: 1791
% 0.22/0.54  % (12814)Time elapsed: 0.115 s
% 0.22/0.54  % (12814)------------------------------
% 0.22/0.54  % (12814)------------------------------
% 0.22/0.54  % (12831)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (12846)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (12817)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (12838)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (12839)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (12845)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (12818)Refutation not found, incomplete strategy% (12818)------------------------------
% 0.22/0.54  % (12818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12818)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12818)Memory used [KB]: 6268
% 0.22/0.54  % (12818)Time elapsed: 0.128 s
% 0.22/0.54  % (12818)------------------------------
% 0.22/0.54  % (12818)------------------------------
% 0.22/0.54  % (12842)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (12844)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (12816)Refutation not found, incomplete strategy% (12816)------------------------------
% 0.22/0.54  % (12816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12816)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12816)Memory used [KB]: 10746
% 0.22/0.54  % (12816)Time elapsed: 0.125 s
% 0.22/0.54  % (12816)------------------------------
% 0.22/0.54  % (12816)------------------------------
% 0.22/0.54  % (12843)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (12820)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (12835)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (12837)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (12841)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (12825)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (12839)Refutation not found, incomplete strategy% (12839)------------------------------
% 0.22/0.55  % (12839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (12839)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (12839)Memory used [KB]: 10746
% 0.22/0.55  % (12839)Time elapsed: 0.133 s
% 0.22/0.55  % (12839)------------------------------
% 0.22/0.55  % (12839)------------------------------
% 0.22/0.55  % (12827)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (12827)Refutation not found, incomplete strategy% (12827)------------------------------
% 0.22/0.55  % (12827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f94,f155,f117])).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~sP0(X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f116,f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~sP0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~sP0(X0))),
% 0.22/0.55    inference(nnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~sP0(X0))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~sP0(X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f114,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X0] : (~sP0(X0) | v1_funct_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~sP0(X0)) )),
% 0.22/0.55    inference(resolution,[],[f106,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~sP0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(k9_relat_1(X2,X3),X1) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f105])).
% 0.22/0.55  % (12833)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r1_tarski(k9_relat_1(X2,X3),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(superposition,[],[f69,f68])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  % (12821)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.55    inference(flattening,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.55    inference(ennf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_2)).
% 0.22/0.55  fof(f155,plain,(
% 0.22/0.55    ~r1_tarski(k9_relat_1(sK7,sK6),k2_relat_1(sK7))),
% 0.22/0.55    inference(subsumption_resolution,[],[f153,f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    k1_xboole_0 != sK5),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ~r1_tarski(k7_relset_1(k1_tarski(sK4),sK5,sK7,sK6),k1_tarski(k1_funct_1(sK7,sK4))) & k1_xboole_0 != sK5 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5))) & v1_funct_2(sK7,k1_tarski(sK4),sK5) & v1_funct_1(sK7)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f18,f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK4),sK5,sK7,sK6),k1_tarski(k1_funct_1(sK7,sK4))) & k1_xboole_0 != sK5 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5))) & v1_funct_2(sK7,k1_tarski(sK4),sK5) & v1_funct_1(sK7))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 0.22/0.55    inference(flattening,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 0.22/0.55    inference(ennf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.22/0.55    inference(negated_conjecture,[],[f15])).
% 0.22/0.55  fof(f15,conjecture,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 0.22/0.55  fof(f153,plain,(
% 0.22/0.55    ~r1_tarski(k9_relat_1(sK7,sK6),k2_relat_1(sK7)) | k1_xboole_0 = sK5),
% 0.22/0.55    inference(resolution,[],[f149,f63])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f43])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) | ~r1_tarski(k9_relat_1(sK7,sK6),k2_relat_1(sK7))),
% 0.22/0.55    inference(superposition,[],[f108,f141])).
% 0.22/0.55  fof(f141,plain,(
% 0.22/0.55    k6_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)) = k2_relat_1(sK7) | sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)),
% 0.22/0.55    inference(subsumption_resolution,[],[f140,f93])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    v1_relat_1(sK7)),
% 0.22/0.55    inference(resolution,[],[f80,f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)))),
% 0.22/0.55    inference(definition_unfolding,[],[f46,f78])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f49,f77])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f54,f76])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f56,f75])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f67,f74])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f70,f73])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f71,f72])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.55  % (12827)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5)))),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  
% 0.22/0.55  % (12827)Memory used [KB]: 10618
% 0.22/0.55  fof(f140,plain,(
% 0.22/0.55    k6_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)) = k2_relat_1(sK7) | ~v1_relat_1(sK7) | sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)),
% 0.22/0.55    inference(subsumption_resolution,[],[f139,f44])).
% 0.22/0.55  % (12827)Time elapsed: 0.143 s
% 0.22/0.55  % (12827)------------------------------
% 0.22/0.55  % (12827)------------------------------
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    v1_funct_1(sK7)),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f139,plain,(
% 0.22/0.55    k6_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)) = k2_relat_1(sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)),
% 0.22/0.55    inference(equality_resolution,[],[f125])).
% 0.22/0.55  fof(f125,plain,(
% 0.22/0.55    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK7) | k2_relat_1(X0) = k6_enumset1(k1_funct_1(X0,sK4),k1_funct_1(X0,sK4),k1_funct_1(X0,sK4),k1_funct_1(X0,sK4),k1_funct_1(X0,sK4),k1_funct_1(X0,sK4),k1_funct_1(X0,sK4),k1_funct_1(X0,sK4)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)) )),
% 0.22/0.55    inference(superposition,[],[f82,f111])).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_relat_1(sK7) | sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)),
% 0.22/0.55    inference(subsumption_resolution,[],[f110,f81])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    v1_funct_2(sK7,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)),
% 0.22/0.55    inference(definition_unfolding,[],[f45,f78])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    v1_funct_2(sK7,k1_tarski(sK4),sK5)),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f110,plain,(
% 0.22/0.55    ~v1_funct_2(sK7,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) | sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_relat_1(sK7)),
% 0.22/0.55    inference(resolution,[],[f97,f80])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f95,f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(definition_folding,[],[f26,f34,f33,f32])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(flattening,[],[f25])).
% 0.22/0.55  % (12832)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | ~sP2(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.22/0.55    inference(superposition,[],[f61,f58])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 0.22/0.55    inference(rectify,[],[f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f33])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_relat_1(X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | k2_relat_1(X1) = k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f55,f78,f78])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.22/0.55  fof(f108,plain,(
% 0.22/0.55    ~r1_tarski(k9_relat_1(sK7,sK6),k6_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f107,f80])).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    ~r1_tarski(k9_relat_1(sK7,sK6),k6_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)))),
% 0.22/0.55    inference(superposition,[],[f79,f68])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ~r1_tarski(k7_relset_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5,sK7,sK6),k6_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)))),
% 0.22/0.55    inference(definition_unfolding,[],[f48,f78,f78])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ~r1_tarski(k7_relset_1(k1_tarski(sK4),sK5,sK7,sK6),k1_tarski(k1_funct_1(sK7,sK4)))),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    sP0(sK7)),
% 0.22/0.55    inference(resolution,[],[f93,f87])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    ~v1_relat_1(sK7) | sP0(sK7)),
% 0.22/0.55    inference(resolution,[],[f53,f44])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_funct_1(X0) | sP0(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0] : (sP0(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(definition_folding,[],[f20,f30])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (12846)------------------------------
% 0.22/0.55  % (12846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (12846)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (12846)Memory used [KB]: 1791
% 0.22/0.55  % (12846)Time elapsed: 0.126 s
% 0.22/0.55  % (12846)------------------------------
% 0.22/0.55  % (12846)------------------------------
% 0.22/0.55  % (12832)Refutation not found, incomplete strategy% (12832)------------------------------
% 0.22/0.55  % (12832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (12832)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (12832)Memory used [KB]: 6140
% 0.22/0.55  % (12832)Time elapsed: 0.002 s
% 0.22/0.55  % (12832)------------------------------
% 0.22/0.55  % (12832)------------------------------
% 0.22/0.55  % (12810)Success in time 0.186 s
%------------------------------------------------------------------------------

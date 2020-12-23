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
% DateTime   : Thu Dec  3 13:04:32 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 656 expanded)
%              Number of leaves         :   20 ( 191 expanded)
%              Depth                    :   20
%              Number of atoms          :  250 (1409 expanded)
%              Number of equality atoms :  102 ( 623 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f461,plain,(
    $false ),
    inference(subsumption_resolution,[],[f460,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f460,plain,(
    ~ r1_tarski(k1_xboole_0,k3_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) ),
    inference(forward_demodulation,[],[f446,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f446,plain,(
    ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k3_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) ),
    inference(backward_demodulation,[],[f188,f430])).

fof(f430,plain,(
    k1_xboole_0 = sK3 ),
    inference(unit_resulting_resolution,[],[f50,f400,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f400,plain,(
    r1_tarski(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f392,f91])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f64])).

% (17496)Refutation not found, incomplete strategy% (17496)------------------------------
% (17496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17496)Termination reason: Refutation not found, incomplete strategy

% (17496)Memory used [KB]: 10746
% (17496)Time elapsed: 0.146 s
% (17496)------------------------------
% (17496)------------------------------
% (17504)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (17510)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% (17484)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% (17498)Refutation not found, incomplete strategy% (17498)------------------------------
% (17498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17498)Termination reason: Refutation not found, incomplete strategy

% (17498)Memory used [KB]: 1791
% (17498)Time elapsed: 0.125 s
% (17498)------------------------------
% (17498)------------------------------
% (17503)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (17485)Refutation not found, incomplete strategy% (17485)------------------------------
% (17485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17485)Termination reason: Refutation not found, incomplete strategy

% (17485)Memory used [KB]: 1663
% (17485)Time elapsed: 0.145 s
% (17485)------------------------------
% (17485)------------------------------
% (17502)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (17502)Refutation not found, incomplete strategy% (17502)------------------------------
% (17502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17502)Termination reason: Refutation not found, incomplete strategy

% (17502)Memory used [KB]: 1791
% (17502)Time elapsed: 0.157 s
% (17502)------------------------------
% (17502)------------------------------
% (17501)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (17501)Refutation not found, incomplete strategy% (17501)------------------------------
% (17501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17501)Termination reason: Refutation not found, incomplete strategy

% (17501)Memory used [KB]: 1791
% (17501)Time elapsed: 0.159 s
% (17501)------------------------------
% (17501)------------------------------
fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f392,plain,(
    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) ),
    inference(backward_demodulation,[],[f180,f368])).

fof(f368,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f228,f185,f228,f228,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2))
      | k3_enumset1(X2,X2,X2,X2,X2) = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f69,f78,f79,f79,f78])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f78])).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f185,plain,(
    r1_tarski(k1_relat_1(sK3),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f114,f115,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f55,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f115,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f81,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f47,f79])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

% (17509)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f114,plain,(
    v4_relat_1(sK3,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f81,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f228,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f118,f192])).

fof(f192,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f191,f115])).

fof(f191,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f190,f46])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f190,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f188,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k3_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k3_enumset1(X0,X0,X0,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f56,f79,f79])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f118,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f115,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f180,plain,(
    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK1)) ),
    inference(unit_resulting_resolution,[],[f140,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f140,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) ),
    inference(unit_resulting_resolution,[],[f88,f81,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f188,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k3_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f80,f137])).

fof(f137,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) ),
    inference(unit_resulting_resolution,[],[f81,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f80,plain,(
    ~ r1_tarski(k7_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k3_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f49,f79,f79])).

fof(f49,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:47:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.52  % (17486)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (17506)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (17490)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (17489)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (17488)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (17499)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (17494)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (17505)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (17487)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (17491)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (17496)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (17485)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (17495)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (17498)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (17508)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (17513)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (17508)Refutation not found, incomplete strategy% (17508)------------------------------
% 0.21/0.55  % (17508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17508)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17508)Memory used [KB]: 10618
% 0.21/0.55  % (17508)Time elapsed: 0.131 s
% 0.21/0.55  % (17508)------------------------------
% 0.21/0.55  % (17508)------------------------------
% 0.21/0.55  % (17511)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (17513)Refutation not found, incomplete strategy% (17513)------------------------------
% 0.21/0.55  % (17513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17513)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17513)Memory used [KB]: 1663
% 0.21/0.55  % (17513)Time elapsed: 0.128 s
% 0.21/0.55  % (17513)------------------------------
% 0.21/0.55  % (17513)------------------------------
% 0.21/0.55  % (17511)Refutation not found, incomplete strategy% (17511)------------------------------
% 0.21/0.55  % (17511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17511)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17511)Memory used [KB]: 6268
% 0.21/0.55  % (17511)Time elapsed: 0.125 s
% 0.21/0.55  % (17511)------------------------------
% 0.21/0.55  % (17511)------------------------------
% 0.21/0.55  % (17497)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (17507)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (17492)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (17494)Refutation not found, incomplete strategy% (17494)------------------------------
% 0.21/0.55  % (17494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17494)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17494)Memory used [KB]: 10746
% 0.21/0.55  % (17494)Time elapsed: 0.127 s
% 0.21/0.55  % (17494)------------------------------
% 0.21/0.55  % (17494)------------------------------
% 0.21/0.55  % (17512)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (17512)Refutation not found, incomplete strategy% (17512)------------------------------
% 0.21/0.55  % (17512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17512)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17512)Memory used [KB]: 10746
% 0.21/0.55  % (17512)Time elapsed: 0.138 s
% 0.21/0.55  % (17512)------------------------------
% 0.21/0.55  % (17512)------------------------------
% 0.21/0.55  % (17500)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (17500)Refutation not found, incomplete strategy% (17500)------------------------------
% 0.21/0.56  % (17500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17500)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (17500)Memory used [KB]: 10618
% 0.21/0.56  % (17500)Time elapsed: 0.141 s
% 0.21/0.56  % (17500)------------------------------
% 0.21/0.56  % (17500)------------------------------
% 1.46/0.56  % (17493)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.46/0.56  % (17488)Refutation found. Thanks to Tanya!
% 1.46/0.56  % SZS status Theorem for theBenchmark
% 1.46/0.56  % SZS output start Proof for theBenchmark
% 1.46/0.56  fof(f461,plain,(
% 1.46/0.56    $false),
% 1.46/0.56    inference(subsumption_resolution,[],[f460,f50])).
% 1.46/0.56  fof(f50,plain,(
% 1.46/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f2])).
% 1.46/0.56  fof(f2,axiom,(
% 1.46/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.46/0.56  fof(f460,plain,(
% 1.46/0.56    ~r1_tarski(k1_xboole_0,k3_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))),
% 1.46/0.56    inference(forward_demodulation,[],[f446,f51])).
% 1.46/0.56  fof(f51,plain,(
% 1.46/0.56    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f11])).
% 1.46/0.56  fof(f11,axiom,(
% 1.46/0.56    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 1.46/0.56  fof(f446,plain,(
% 1.46/0.56    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k3_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))),
% 1.46/0.56    inference(backward_demodulation,[],[f188,f430])).
% 1.46/0.56  fof(f430,plain,(
% 1.46/0.56    k1_xboole_0 = sK3),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f50,f400,f60])).
% 1.46/0.56  fof(f60,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f40])).
% 1.46/0.56  fof(f40,plain,(
% 1.46/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.46/0.56    inference(flattening,[],[f39])).
% 1.46/0.56  fof(f39,plain,(
% 1.46/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.46/0.56    inference(nnf_transformation,[],[f1])).
% 1.46/0.56  fof(f1,axiom,(
% 1.46/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.46/0.56  fof(f400,plain,(
% 1.46/0.56    r1_tarski(sK3,k1_xboole_0)),
% 1.46/0.56    inference(forward_demodulation,[],[f392,f91])).
% 1.46/0.56  fof(f91,plain,(
% 1.46/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.46/0.56    inference(equality_resolution,[],[f64])).
% 1.46/0.56  % (17496)Refutation not found, incomplete strategy% (17496)------------------------------
% 1.46/0.56  % (17496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (17496)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (17496)Memory used [KB]: 10746
% 1.46/0.56  % (17496)Time elapsed: 0.146 s
% 1.46/0.56  % (17496)------------------------------
% 1.46/0.56  % (17496)------------------------------
% 1.46/0.56  % (17504)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.46/0.56  % (17510)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.46/0.56  % (17484)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.46/0.57  % (17498)Refutation not found, incomplete strategy% (17498)------------------------------
% 1.46/0.57  % (17498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (17498)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.57  
% 1.46/0.57  % (17498)Memory used [KB]: 1791
% 1.46/0.57  % (17498)Time elapsed: 0.125 s
% 1.46/0.57  % (17498)------------------------------
% 1.46/0.57  % (17498)------------------------------
% 1.46/0.57  % (17503)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.46/0.57  % (17485)Refutation not found, incomplete strategy% (17485)------------------------------
% 1.46/0.57  % (17485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (17485)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.57  
% 1.46/0.57  % (17485)Memory used [KB]: 1663
% 1.46/0.57  % (17485)Time elapsed: 0.145 s
% 1.46/0.57  % (17485)------------------------------
% 1.46/0.57  % (17485)------------------------------
% 1.46/0.57  % (17502)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.46/0.57  % (17502)Refutation not found, incomplete strategy% (17502)------------------------------
% 1.46/0.57  % (17502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (17502)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.57  
% 1.46/0.57  % (17502)Memory used [KB]: 1791
% 1.46/0.57  % (17502)Time elapsed: 0.157 s
% 1.46/0.57  % (17502)------------------------------
% 1.46/0.57  % (17502)------------------------------
% 1.46/0.58  % (17501)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.63/0.58  % (17501)Refutation not found, incomplete strategy% (17501)------------------------------
% 1.63/0.58  % (17501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (17501)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (17501)Memory used [KB]: 1791
% 1.63/0.58  % (17501)Time elapsed: 0.159 s
% 1.63/0.58  % (17501)------------------------------
% 1.63/0.58  % (17501)------------------------------
% 1.63/0.58  fof(f64,plain,(
% 1.63/0.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.63/0.58    inference(cnf_transformation,[],[f43])).
% 1.63/0.58  fof(f43,plain,(
% 1.63/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.63/0.58    inference(flattening,[],[f42])).
% 1.63/0.58  fof(f42,plain,(
% 1.63/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.63/0.58    inference(nnf_transformation,[],[f8])).
% 1.63/0.58  fof(f8,axiom,(
% 1.63/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.63/0.58  fof(f392,plain,(
% 1.63/0.58    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1))),
% 1.63/0.58    inference(backward_demodulation,[],[f180,f368])).
% 1.63/0.58  fof(f368,plain,(
% 1.63/0.58    k1_xboole_0 = k1_relat_1(sK3)),
% 1.63/0.58    inference(unit_resulting_resolution,[],[f228,f185,f228,f228,f87])).
% 1.63/0.58  fof(f87,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2)) | k3_enumset1(X2,X2,X2,X2,X2) = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X2) = X0) )),
% 1.63/0.58    inference(definition_unfolding,[],[f69,f78,f79,f79,f78])).
% 1.63/0.58  fof(f79,plain,(
% 1.63/0.58    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.63/0.58    inference(definition_unfolding,[],[f52,f78])).
% 1.63/0.58  fof(f52,plain,(
% 1.63/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f3])).
% 1.63/0.58  fof(f3,axiom,(
% 1.63/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.63/0.58  fof(f78,plain,(
% 1.63/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.63/0.58    inference(definition_unfolding,[],[f53,f77])).
% 1.63/0.58  fof(f77,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.63/0.58    inference(definition_unfolding,[],[f66,f74])).
% 1.63/0.58  fof(f74,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f6])).
% 1.63/0.58  fof(f6,axiom,(
% 1.63/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.63/0.58  fof(f66,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f5])).
% 1.63/0.58  fof(f5,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.63/0.58  fof(f53,plain,(
% 1.63/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f4])).
% 1.63/0.58  fof(f4,axiom,(
% 1.63/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.63/0.58  fof(f69,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f45])).
% 1.63/0.58  fof(f45,plain,(
% 1.63/0.58    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.63/0.58    inference(flattening,[],[f44])).
% 1.63/0.58  fof(f44,plain,(
% 1.63/0.58    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.63/0.58    inference(nnf_transformation,[],[f33])).
% 1.63/0.58  fof(f33,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.63/0.58    inference(ennf_transformation,[],[f7])).
% 1.63/0.58  fof(f7,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.63/0.58  fof(f185,plain,(
% 1.63/0.58    r1_tarski(k1_relat_1(sK3),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.63/0.58    inference(unit_resulting_resolution,[],[f114,f115,f113])).
% 1.63/0.58  fof(f113,plain,(
% 1.63/0.58    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 1.63/0.58    inference(duplicate_literal_removal,[],[f112])).
% 1.63/0.58  fof(f112,plain,(
% 1.63/0.58    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.63/0.58    inference(superposition,[],[f55,f57])).
% 1.63/0.58  fof(f57,plain,(
% 1.63/0.58    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f30])).
% 1.63/0.58  fof(f30,plain,(
% 1.63/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.63/0.58    inference(flattening,[],[f29])).
% 1.63/0.58  fof(f29,plain,(
% 1.63/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.63/0.58    inference(ennf_transformation,[],[f12])).
% 1.63/0.58  fof(f12,axiom,(
% 1.63/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.63/0.58  fof(f55,plain,(
% 1.63/0.58    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f26])).
% 1.63/0.58  fof(f26,plain,(
% 1.63/0.58    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.63/0.58    inference(ennf_transformation,[],[f13])).
% 1.63/0.58  fof(f13,axiom,(
% 1.63/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 1.63/0.58  fof(f115,plain,(
% 1.63/0.58    v1_relat_1(sK3)),
% 1.63/0.58    inference(unit_resulting_resolution,[],[f81,f67])).
% 1.63/0.58  fof(f67,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f31])).
% 1.63/0.58  fof(f31,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.58    inference(ennf_transformation,[],[f15])).
% 1.63/0.58  fof(f15,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.63/0.58  fof(f81,plain,(
% 1.63/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)))),
% 1.63/0.58    inference(definition_unfolding,[],[f47,f79])).
% 1.63/0.58  fof(f47,plain,(
% 1.63/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.63/0.58    inference(cnf_transformation,[],[f38])).
% 1.63/0.58  fof(f38,plain,(
% 1.63/0.58    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 1.63/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f37])).
% 1.63/0.58  fof(f37,plain,(
% 1.63/0.58    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 1.63/0.58    introduced(choice_axiom,[])).
% 1.63/0.58  % (17509)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.63/0.58  fof(f24,plain,(
% 1.63/0.58    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.63/0.58    inference(flattening,[],[f23])).
% 1.63/0.58  fof(f23,plain,(
% 1.63/0.58    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.63/0.58    inference(ennf_transformation,[],[f21])).
% 1.63/0.58  fof(f21,plain,(
% 1.63/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.63/0.58    inference(pure_predicate_removal,[],[f20])).
% 1.63/0.58  fof(f20,negated_conjecture,(
% 1.63/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.63/0.58    inference(negated_conjecture,[],[f19])).
% 1.63/0.58  fof(f19,conjecture,(
% 1.63/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 1.63/0.58  fof(f114,plain,(
% 1.63/0.58    v4_relat_1(sK3,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.63/0.58    inference(unit_resulting_resolution,[],[f81,f68])).
% 1.63/0.58  fof(f68,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f32])).
% 1.63/0.58  fof(f32,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.58    inference(ennf_transformation,[],[f22])).
% 1.63/0.58  fof(f22,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.63/0.58    inference(pure_predicate_removal,[],[f16])).
% 1.63/0.58  fof(f16,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.63/0.58  fof(f228,plain,(
% 1.63/0.58    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3)),
% 1.63/0.58    inference(unit_resulting_resolution,[],[f118,f192])).
% 1.63/0.58  fof(f192,plain,(
% 1.63/0.58    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3) | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 1.63/0.58    inference(subsumption_resolution,[],[f191,f115])).
% 1.63/0.58  fof(f191,plain,(
% 1.63/0.58    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.63/0.58    inference(subsumption_resolution,[],[f190,f46])).
% 1.63/0.58  fof(f46,plain,(
% 1.63/0.58    v1_funct_1(sK3)),
% 1.63/0.58    inference(cnf_transformation,[],[f38])).
% 1.63/0.58  fof(f190,plain,(
% 1.63/0.58    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.63/0.58    inference(superposition,[],[f188,f82])).
% 1.63/0.58  fof(f82,plain,(
% 1.63/0.58    ( ! [X0,X1] : (k2_relat_1(X1) = k3_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | k1_relat_1(X1) != k3_enumset1(X0,X0,X0,X0,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.63/0.58    inference(definition_unfolding,[],[f56,f79,f79])).
% 1.63/0.58  fof(f56,plain,(
% 1.63/0.58    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f28])).
% 1.63/0.58  fof(f28,plain,(
% 1.63/0.58    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.63/0.58    inference(flattening,[],[f27])).
% 1.63/0.58  fof(f27,plain,(
% 1.63/0.58    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.63/0.58    inference(ennf_transformation,[],[f14])).
% 1.63/0.58  fof(f14,axiom,(
% 1.63/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 1.63/0.58  fof(f118,plain,(
% 1.63/0.58    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))) )),
% 1.63/0.58    inference(unit_resulting_resolution,[],[f115,f54])).
% 1.63/0.58  fof(f54,plain,(
% 1.63/0.58    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f25])).
% 1.63/0.58  fof(f25,plain,(
% 1.63/0.58    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.63/0.58    inference(ennf_transformation,[],[f10])).
% 1.63/0.58  fof(f10,axiom,(
% 1.63/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 1.63/0.58  fof(f180,plain,(
% 1.63/0.58    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK1))),
% 1.63/0.58    inference(unit_resulting_resolution,[],[f140,f61])).
% 1.63/0.58  fof(f61,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f41])).
% 1.63/0.58  fof(f41,plain,(
% 1.63/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.63/0.58    inference(nnf_transformation,[],[f9])).
% 1.63/0.58  fof(f9,axiom,(
% 1.63/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.63/0.58  fof(f140,plain,(
% 1.63/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))),
% 1.63/0.58    inference(unit_resulting_resolution,[],[f88,f81,f76])).
% 1.63/0.58  fof(f76,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f36])).
% 1.63/0.58  fof(f36,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.63/0.58    inference(flattening,[],[f35])).
% 1.63/0.58  fof(f35,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.63/0.58    inference(ennf_transformation,[],[f18])).
% 1.63/0.58  fof(f18,axiom,(
% 1.63/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 1.63/0.58  fof(f88,plain,(
% 1.63/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.63/0.58    inference(equality_resolution,[],[f59])).
% 1.63/0.58  fof(f59,plain,(
% 1.63/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.63/0.58    inference(cnf_transformation,[],[f40])).
% 1.63/0.58  fof(f188,plain,(
% 1.63/0.58    ~r1_tarski(k9_relat_1(sK3,sK2),k3_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.63/0.58    inference(backward_demodulation,[],[f80,f137])).
% 1.63/0.58  fof(f137,plain,(
% 1.63/0.58    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0)) )),
% 1.63/0.58    inference(unit_resulting_resolution,[],[f81,f75])).
% 1.63/0.58  fof(f75,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f34])).
% 1.63/0.58  fof(f34,plain,(
% 1.63/0.58    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.58    inference(ennf_transformation,[],[f17])).
% 1.63/0.58  fof(f17,axiom,(
% 1.63/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.63/0.58  fof(f80,plain,(
% 1.63/0.58    ~r1_tarski(k7_relset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k3_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.63/0.58    inference(definition_unfolding,[],[f49,f79,f79])).
% 1.63/0.58  fof(f49,plain,(
% 1.63/0.58    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.63/0.58    inference(cnf_transformation,[],[f38])).
% 1.63/0.58  % SZS output end Proof for theBenchmark
% 1.63/0.58  % (17488)------------------------------
% 1.63/0.58  % (17488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (17488)Termination reason: Refutation
% 1.63/0.58  
% 1.63/0.58  % (17488)Memory used [KB]: 1918
% 1.63/0.58  % (17488)Time elapsed: 0.143 s
% 1.63/0.58  % (17488)------------------------------
% 1.63/0.58  % (17488)------------------------------
% 1.63/0.58  % (17483)Success in time 0.206 s
%------------------------------------------------------------------------------

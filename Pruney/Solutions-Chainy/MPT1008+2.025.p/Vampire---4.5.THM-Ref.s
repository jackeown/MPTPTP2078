%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:11 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 567 expanded)
%              Number of leaves         :   16 ( 167 expanded)
%              Depth                    :   18
%              Number of atoms          :  262 (1432 expanded)
%              Number of equality atoms :   88 ( 697 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f222,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f92,f220,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f73,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f220,plain,(
    ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f216,f171])).

fof(f171,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f165,f50])).

fof(f50,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f165,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(backward_demodulation,[],[f118,f155])).

fof(f155,plain,(
    k1_xboole_0 = sK2 ),
    inference(unit_resulting_resolution,[],[f98,f124,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f124,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f108,f109,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f66,f78,f78])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f77])).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f109,plain,(
    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f98,f96,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f96,plain,(
    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f80,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f80,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f46,f78])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f108,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f98,f44,f102,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f62,f78,f78])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f102,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f79,f97])).

fof(f97,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f80,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f79,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f48,f78,f78])).

fof(f48,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f98,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f80,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f118,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(subsumption_resolution,[],[f117,f44])).

fof(f117,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f116,f81])).

fof(f81,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f45,f78])).

fof(f45,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f116,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f115,f80])).

fof(f115,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
      | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f114,f47])).

fof(f47,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f34])).

fof(f114,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | k1_xboole_0 = sK1
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
      | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(superposition,[],[f76,f97])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f216,plain,(
    ~ r2_hidden(k1_funct_1(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,
    ( ~ r2_hidden(k1_funct_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ r2_hidden(k1_funct_1(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(resolution,[],[f197,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f75,f77])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f197,plain,(
    ~ r1_tarski(k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f93,f170,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f170,plain,(
    k1_xboole_0 != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f164,f50])).

fof(f164,plain,(
    k2_relat_1(k1_xboole_0) != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) ),
    inference(backward_demodulation,[],[f102,f155])).

fof(f93,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f67,f78])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    ! [X1] : r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f68,f78,f78])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:17:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (6271)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.50  % (6268)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.50  % (6251)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.50  % (6263)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (6252)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (6259)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (6279)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (6260)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (6251)Refutation not found, incomplete strategy% (6251)------------------------------
% 0.21/0.52  % (6251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.52  % (6279)Refutation not found, incomplete strategy% (6279)------------------------------
% 1.29/0.52  % (6279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.52  % (6251)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.52  
% 1.29/0.52  % (6251)Memory used [KB]: 1791
% 1.29/0.52  % (6251)Time elapsed: 0.082 s
% 1.29/0.52  % (6251)------------------------------
% 1.29/0.52  % (6251)------------------------------
% 1.29/0.52  % (6264)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.29/0.52  % (6261)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.29/0.52  % (6250)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.29/0.52  % (6258)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.29/0.52  % (6256)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.53  % (6260)Refutation not found, incomplete strategy% (6260)------------------------------
% 1.29/0.53  % (6260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (6260)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (6260)Memory used [KB]: 10746
% 1.29/0.53  % (6260)Time elapsed: 0.128 s
% 1.29/0.53  % (6260)------------------------------
% 1.29/0.53  % (6260)------------------------------
% 1.29/0.53  % (6264)Refutation not found, incomplete strategy% (6264)------------------------------
% 1.29/0.53  % (6264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (6264)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (6264)Memory used [KB]: 1791
% 1.29/0.53  % (6264)Time elapsed: 0.092 s
% 1.29/0.53  % (6264)------------------------------
% 1.29/0.53  % (6264)------------------------------
% 1.29/0.53  % (6268)Refutation not found, incomplete strategy% (6268)------------------------------
% 1.29/0.53  % (6268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (6268)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (6268)Memory used [KB]: 1791
% 1.29/0.53  % (6268)Time elapsed: 0.109 s
% 1.29/0.53  % (6268)------------------------------
% 1.29/0.53  % (6268)------------------------------
% 1.29/0.53  % (6253)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.29/0.53  % (6266)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.29/0.53  % (6279)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (6279)Memory used [KB]: 1791
% 1.29/0.53  % (6279)Time elapsed: 0.117 s
% 1.29/0.53  % (6279)------------------------------
% 1.29/0.53  % (6279)------------------------------
% 1.29/0.53  % (6266)Refutation not found, incomplete strategy% (6266)------------------------------
% 1.29/0.53  % (6266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (6266)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (6266)Memory used [KB]: 10618
% 1.29/0.53  % (6266)Time elapsed: 0.125 s
% 1.29/0.53  % (6266)------------------------------
% 1.29/0.53  % (6266)------------------------------
% 1.29/0.53  % (6272)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.29/0.53  % (6254)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.29/0.53  % (6255)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.29/0.53  % (6276)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.29/0.53  % (6274)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.29/0.53  % (6276)Refutation not found, incomplete strategy% (6276)------------------------------
% 1.29/0.53  % (6276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (6276)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (6276)Memory used [KB]: 6268
% 1.29/0.53  % (6276)Time elapsed: 0.135 s
% 1.29/0.53  % (6276)------------------------------
% 1.29/0.53  % (6276)------------------------------
% 1.29/0.53  % (6265)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.29/0.53  % (6262)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.29/0.54  % (6257)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.48/0.54  % (6269)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.48/0.54  % (6278)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.48/0.55  % (6275)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.48/0.55  % (6261)Refutation found. Thanks to Tanya!
% 1.48/0.55  % SZS status Theorem for theBenchmark
% 1.48/0.55  % SZS output start Proof for theBenchmark
% 1.48/0.55  fof(f222,plain,(
% 1.48/0.55    $false),
% 1.48/0.55    inference(unit_resulting_resolution,[],[f92,f220,f89])).
% 1.48/0.55  fof(f89,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.48/0.55    inference(definition_unfolding,[],[f73,f77])).
% 1.48/0.55  fof(f77,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.48/0.55    inference(definition_unfolding,[],[f59,f69])).
% 1.48/0.55  fof(f69,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f5])).
% 1.48/0.55  fof(f5,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.48/0.55  fof(f59,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f4])).
% 1.48/0.55  fof(f4,axiom,(
% 1.48/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.48/0.55  fof(f73,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f43])).
% 1.48/0.55  fof(f43,plain,(
% 1.48/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.48/0.55    inference(flattening,[],[f42])).
% 1.48/0.55  fof(f42,plain,(
% 1.48/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.48/0.55    inference(nnf_transformation,[],[f7])).
% 1.48/0.55  fof(f7,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.48/0.55  fof(f220,plain,(
% 1.48/0.55    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.48/0.55    inference(unit_resulting_resolution,[],[f216,f171])).
% 1.48/0.55  fof(f171,plain,(
% 1.48/0.55    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)) )),
% 1.48/0.55    inference(forward_demodulation,[],[f165,f50])).
% 1.48/0.55  fof(f50,plain,(
% 1.48/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.48/0.55    inference(cnf_transformation,[],[f9])).
% 1.48/0.55  fof(f9,axiom,(
% 1.48/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.48/0.55  fof(f165,plain,(
% 1.48/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0)) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.48/0.55    inference(backward_demodulation,[],[f118,f155])).
% 1.48/0.55  fof(f155,plain,(
% 1.48/0.55    k1_xboole_0 = sK2),
% 1.48/0.55    inference(unit_resulting_resolution,[],[f98,f124,f53])).
% 1.48/0.55  fof(f53,plain,(
% 1.48/0.55    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f23])).
% 1.48/0.55  fof(f23,plain,(
% 1.48/0.55    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.48/0.55    inference(flattening,[],[f22])).
% 1.48/0.55  fof(f22,plain,(
% 1.48/0.55    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.48/0.55    inference(ennf_transformation,[],[f10])).
% 1.48/0.55  fof(f10,axiom,(
% 1.48/0.55    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.48/0.55  fof(f124,plain,(
% 1.48/0.55    k1_xboole_0 = k1_relat_1(sK2)),
% 1.48/0.55    inference(unit_resulting_resolution,[],[f108,f109,f86])).
% 1.48/0.55  fof(f86,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.48/0.55    inference(definition_unfolding,[],[f66,f78,f78])).
% 1.48/0.55  fof(f78,plain,(
% 1.48/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.48/0.55    inference(definition_unfolding,[],[f52,f77])).
% 1.48/0.55  fof(f52,plain,(
% 1.48/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f3])).
% 1.48/0.55  fof(f3,axiom,(
% 1.48/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.48/0.55  fof(f66,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.48/0.55    inference(cnf_transformation,[],[f41])).
% 1.48/0.55  fof(f41,plain,(
% 1.48/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.48/0.55    inference(flattening,[],[f40])).
% 1.48/0.55  fof(f40,plain,(
% 1.48/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.48/0.55    inference(nnf_transformation,[],[f6])).
% 1.48/0.55  fof(f6,axiom,(
% 1.48/0.55    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.48/0.55  fof(f109,plain,(
% 1.48/0.55    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.48/0.55    inference(unit_resulting_resolution,[],[f98,f96,f60])).
% 1.48/0.55  fof(f60,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f37])).
% 1.48/0.55  fof(f37,plain,(
% 1.48/0.55    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.48/0.55    inference(nnf_transformation,[],[f25])).
% 1.48/0.55  fof(f25,plain,(
% 1.48/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.48/0.55    inference(ennf_transformation,[],[f8])).
% 1.48/0.55  fof(f8,axiom,(
% 1.48/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.48/0.55  fof(f96,plain,(
% 1.48/0.55    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.48/0.55    inference(unit_resulting_resolution,[],[f80,f72])).
% 1.48/0.55  fof(f72,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f30])).
% 1.48/0.55  fof(f30,plain,(
% 1.48/0.55    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.55    inference(ennf_transformation,[],[f19])).
% 1.48/0.55  fof(f19,plain,(
% 1.48/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.48/0.55    inference(pure_predicate_removal,[],[f13])).
% 1.48/0.55  fof(f13,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.48/0.55  fof(f80,plain,(
% 1.48/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.48/0.55    inference(definition_unfolding,[],[f46,f78])).
% 1.48/0.55  fof(f46,plain,(
% 1.48/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.48/0.55    inference(cnf_transformation,[],[f34])).
% 1.48/0.55  fof(f34,plain,(
% 1.48/0.55    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 1.48/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f33])).
% 1.48/0.55  fof(f33,plain,(
% 1.48/0.55    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 1.48/0.55    introduced(choice_axiom,[])).
% 1.48/0.55  fof(f21,plain,(
% 1.48/0.55    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.48/0.55    inference(flattening,[],[f20])).
% 1.48/0.55  fof(f20,plain,(
% 1.48/0.55    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.48/0.55    inference(ennf_transformation,[],[f18])).
% 1.48/0.55  fof(f18,negated_conjecture,(
% 1.48/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.48/0.55    inference(negated_conjecture,[],[f17])).
% 1.48/0.55  fof(f17,conjecture,(
% 1.48/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 1.48/0.55  fof(f108,plain,(
% 1.48/0.55    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK2)),
% 1.48/0.55    inference(unit_resulting_resolution,[],[f98,f44,f102,f83])).
% 1.48/0.55  fof(f83,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.48/0.55    inference(definition_unfolding,[],[f62,f78,f78])).
% 1.48/0.55  fof(f62,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f27])).
% 1.48/0.55  fof(f27,plain,(
% 1.48/0.55    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.48/0.55    inference(flattening,[],[f26])).
% 1.48/0.55  fof(f26,plain,(
% 1.48/0.55    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.48/0.55    inference(ennf_transformation,[],[f11])).
% 1.48/0.55  fof(f11,axiom,(
% 1.48/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.48/0.55  fof(f102,plain,(
% 1.48/0.55    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)),
% 1.48/0.55    inference(backward_demodulation,[],[f79,f97])).
% 1.48/0.55  fof(f97,plain,(
% 1.48/0.55    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)),
% 1.48/0.55    inference(unit_resulting_resolution,[],[f80,f71])).
% 1.48/0.55  fof(f71,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f29])).
% 1.48/0.55  fof(f29,plain,(
% 1.48/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.55    inference(ennf_transformation,[],[f14])).
% 1.48/0.55  fof(f14,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.48/0.55  fof(f79,plain,(
% 1.48/0.55    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 1.48/0.55    inference(definition_unfolding,[],[f48,f78,f78])).
% 1.48/0.55  fof(f48,plain,(
% 1.48/0.55    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 1.48/0.55    inference(cnf_transformation,[],[f34])).
% 1.48/0.55  fof(f44,plain,(
% 1.48/0.55    v1_funct_1(sK2)),
% 1.48/0.55    inference(cnf_transformation,[],[f34])).
% 1.48/0.55  fof(f98,plain,(
% 1.48/0.55    v1_relat_1(sK2)),
% 1.48/0.55    inference(unit_resulting_resolution,[],[f80,f70])).
% 1.48/0.55  fof(f70,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f28])).
% 1.48/0.55  fof(f28,plain,(
% 1.48/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.55    inference(ennf_transformation,[],[f12])).
% 1.48/0.55  fof(f12,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.48/0.55  fof(f118,plain,(
% 1.48/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f117,f44])).
% 1.48/0.55  fof(f117,plain,(
% 1.48/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_funct_1(sK2)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f116,f81])).
% 1.48/0.55  fof(f81,plain,(
% 1.48/0.55    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.48/0.55    inference(definition_unfolding,[],[f45,f78])).
% 1.48/0.55  fof(f45,plain,(
% 1.48/0.55    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.48/0.55    inference(cnf_transformation,[],[f34])).
% 1.48/0.55  fof(f116,plain,(
% 1.48/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~v1_funct_1(sK2)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f115,f80])).
% 1.48/0.55  fof(f115,plain,(
% 1.48/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~v1_funct_1(sK2)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f114,f47])).
% 1.48/0.55  fof(f47,plain,(
% 1.48/0.55    k1_xboole_0 != sK1),
% 1.48/0.55    inference(cnf_transformation,[],[f34])).
% 1.48/0.55  fof(f114,plain,(
% 1.48/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | k1_xboole_0 = sK1 | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~v1_funct_1(sK2)) )),
% 1.48/0.55    inference(superposition,[],[f76,f97])).
% 1.48/0.55  fof(f76,plain,(
% 1.48/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f32])).
% 1.48/0.55  fof(f32,plain,(
% 1.48/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.48/0.55    inference(flattening,[],[f31])).
% 1.48/0.55  fof(f31,plain,(
% 1.48/0.55    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.48/0.55    inference(ennf_transformation,[],[f16])).
% 1.48/0.55  fof(f16,axiom,(
% 1.48/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 1.48/0.55  fof(f216,plain,(
% 1.48/0.55    ~r2_hidden(k1_funct_1(k1_xboole_0,sK0),k1_xboole_0)),
% 1.48/0.55    inference(duplicate_literal_removal,[],[f215])).
% 1.48/0.55  fof(f215,plain,(
% 1.48/0.55    ~r2_hidden(k1_funct_1(k1_xboole_0,sK0),k1_xboole_0) | ~r2_hidden(k1_funct_1(k1_xboole_0,sK0),k1_xboole_0)),
% 1.48/0.55    inference(resolution,[],[f197,f87])).
% 1.48/0.55  fof(f87,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.48/0.55    inference(definition_unfolding,[],[f75,f77])).
% 1.48/0.55  fof(f75,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f43])).
% 1.48/0.55  fof(f197,plain,(
% 1.48/0.55    ~r1_tarski(k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)),k1_xboole_0)),
% 1.48/0.55    inference(unit_resulting_resolution,[],[f93,f170,f65])).
% 1.48/0.55  fof(f65,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f39])).
% 1.48/0.55  fof(f39,plain,(
% 1.48/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.55    inference(flattening,[],[f38])).
% 1.48/0.55  fof(f38,plain,(
% 1.48/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.55    inference(nnf_transformation,[],[f1])).
% 1.48/0.55  fof(f1,axiom,(
% 1.48/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.48/0.55  fof(f170,plain,(
% 1.48/0.55    k1_xboole_0 != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))),
% 1.48/0.55    inference(forward_demodulation,[],[f164,f50])).
% 1.48/0.55  fof(f164,plain,(
% 1.48/0.55    k2_relat_1(k1_xboole_0) != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))),
% 1.48/0.55    inference(backward_demodulation,[],[f102,f155])).
% 1.48/0.55  fof(f93,plain,(
% 1.48/0.55    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.48/0.55    inference(equality_resolution,[],[f85])).
% 1.48/0.55  fof(f85,plain,(
% 1.48/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 != X0) )),
% 1.48/0.55    inference(definition_unfolding,[],[f67,f78])).
% 1.48/0.55  fof(f67,plain,(
% 1.48/0.55    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 1.48/0.55    inference(cnf_transformation,[],[f41])).
% 1.48/0.55  fof(f92,plain,(
% 1.48/0.55    ( ! [X1] : (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 1.48/0.55    inference(equality_resolution,[],[f84])).
% 1.48/0.55  fof(f84,plain,(
% 1.48/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) != X0) )),
% 1.48/0.55    inference(definition_unfolding,[],[f68,f78,f78])).
% 1.48/0.55  fof(f68,plain,(
% 1.48/0.55    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) != X0) )),
% 1.48/0.55    inference(cnf_transformation,[],[f41])).
% 1.48/0.55  % SZS output end Proof for theBenchmark
% 1.48/0.55  % (6261)------------------------------
% 1.48/0.55  % (6261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (6261)Termination reason: Refutation
% 1.48/0.55  
% 1.48/0.55  % (6261)Memory used [KB]: 6268
% 1.48/0.55  % (6261)Time elapsed: 0.129 s
% 1.48/0.55  % (6261)------------------------------
% 1.48/0.55  % (6261)------------------------------
% 1.48/0.55  % (6278)Refutation not found, incomplete strategy% (6278)------------------------------
% 1.48/0.55  % (6278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (6249)Success in time 0.187 s
%------------------------------------------------------------------------------

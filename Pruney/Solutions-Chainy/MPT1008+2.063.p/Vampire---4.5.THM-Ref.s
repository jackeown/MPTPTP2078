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
% DateTime   : Thu Dec  3 13:04:17 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :  103 (1089 expanded)
%              Number of leaves         :   18 ( 326 expanded)
%              Depth                    :   27
%              Number of atoms          :  329 (2809 expanded)
%              Number of equality atoms :  167 (1569 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f280,plain,(
    $false ),
    inference(subsumption_resolution,[],[f279,f230])).

fof(f230,plain,(
    k1_xboole_0 != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f224,f52])).

fof(f52,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f224,plain,(
    k2_relat_1(k1_xboole_0) != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) ),
    inference(backward_demodulation,[],[f108,f213])).

fof(f213,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f104,f212])).

fof(f212,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f211,f100])).

fof(f100,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f77,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f77,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f43,f75])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f71,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f64,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f34])).

fof(f34,plain,
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

% (32457)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(f211,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f210,f108])).

fof(f210,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f209])).

fof(f209,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f143,f41])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f143,plain,(
    ! [X4] :
      ( ~ v1_funct_1(X4)
      | k2_relat_1(X4) = k2_enumset1(k1_funct_1(X4,sK0),k1_funct_1(X4,sK0),k1_funct_1(X4,sK0),k1_funct_1(X4,sK0))
      | k1_relat_1(sK2) != k1_relat_1(X4)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = k1_relat_1(sK2) ) ),
    inference(superposition,[],[f79,f125])).

fof(f125,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    inference(resolution,[],[f88,f105])).

fof(f105,plain,(
    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f102,f99])).

fof(f99,plain,(
    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f77,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f102,plain,(
    ! [X1] :
      ( ~ v4_relat_1(sK2,X1)
      | r1_tarski(k1_relat_1(sK2),X1) ) ),
    inference(resolution,[],[f100,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | k2_enumset1(X0,X0,X1,X2) = X3 ) ),
    inference(definition_unfolding,[],[f53,f72,f74,f74,f74,f75,f75,f75,f72])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f47,f75,f75])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f104,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f100,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f108,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f76,f107])).

fof(f107,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f48,f77])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f76,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f45,f75,f75])).

fof(f45,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f279,plain,(
    k1_xboole_0 = k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f278,f52])).

fof(f278,plain,(
    k2_relat_1(k1_xboole_0) = k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f277,f221])).

fof(f221,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f100,f213])).

fof(f277,plain,
    ( k2_relat_1(k1_xboole_0) = k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f276,f51])).

fof(f51,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f276,plain,
    ( k2_relat_1(k1_xboole_0) = k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f269,f217])).

fof(f217,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f41,f213])).

% (32439)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f269,plain,(
    ! [X4] :
      ( ~ v1_funct_1(X4)
      | k2_relat_1(X4) = k2_enumset1(k1_funct_1(X4,sK0),k1_funct_1(X4,sK0),k1_funct_1(X4,sK0),k1_funct_1(X4,sK0))
      | k1_xboole_0 != k1_relat_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f79,f245])).

fof(f245,plain,(
    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f235,f66])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f235,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f234,f62])).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f234,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,X0))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(forward_demodulation,[],[f227,f52])).

fof(f227,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X0))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(backward_demodulation,[],[f114,f213])).

fof(f114,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,X0))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(resolution,[],[f113,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f113,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(forward_demodulation,[],[f112,f107])).

fof(f112,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f111,f78])).

fof(f78,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f42,f75])).

fof(f42,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f111,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
      | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f110,f44])).

fof(f44,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f35])).

fof(f110,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | k1_xboole_0 = sK1
      | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
      | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) ) ),
    inference(resolution,[],[f109,f77])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK2,X2,X0)
      | r2_hidden(k1_funct_1(sK2,X1),k2_relset_1(X2,X0,sK2)) ) ),
    inference(resolution,[],[f46,f41])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:11:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (1243316225)
% 0.13/0.37  ipcrm: permission denied for id (1243348994)
% 0.13/0.37  ipcrm: permission denied for id (1243381763)
% 0.13/0.37  ipcrm: permission denied for id (1243414532)
% 0.13/0.37  ipcrm: permission denied for id (1243447301)
% 0.13/0.38  ipcrm: permission denied for id (1247150087)
% 0.13/0.38  ipcrm: permission denied for id (1243545608)
% 0.13/0.38  ipcrm: permission denied for id (1243578377)
% 0.13/0.38  ipcrm: permission denied for id (1247182858)
% 0.13/0.38  ipcrm: permission denied for id (1247215627)
% 0.13/0.38  ipcrm: permission denied for id (1247248396)
% 0.13/0.38  ipcrm: permission denied for id (1243742221)
% 0.13/0.39  ipcrm: permission denied for id (1247281166)
% 0.13/0.39  ipcrm: permission denied for id (1243807759)
% 0.13/0.39  ipcrm: permission denied for id (1247313936)
% 0.13/0.39  ipcrm: permission denied for id (1243873298)
% 0.13/0.39  ipcrm: permission denied for id (1243938836)
% 0.13/0.39  ipcrm: permission denied for id (1243971605)
% 0.13/0.40  ipcrm: permission denied for id (1244004374)
% 0.13/0.40  ipcrm: permission denied for id (1244037143)
% 0.13/0.40  ipcrm: permission denied for id (1244069912)
% 0.13/0.40  ipcrm: permission denied for id (1244102681)
% 0.13/0.40  ipcrm: permission denied for id (1244135450)
% 0.13/0.41  ipcrm: permission denied for id (1247543327)
% 0.13/0.41  ipcrm: permission denied for id (1244332066)
% 0.13/0.41  ipcrm: permission denied for id (1244364835)
% 0.13/0.41  ipcrm: permission denied for id (1247641636)
% 0.13/0.42  ipcrm: permission denied for id (1244430373)
% 0.13/0.42  ipcrm: permission denied for id (1244463142)
% 0.13/0.42  ipcrm: permission denied for id (1247707176)
% 0.13/0.42  ipcrm: permission denied for id (1244528681)
% 0.13/0.42  ipcrm: permission denied for id (1244561450)
% 0.13/0.42  ipcrm: permission denied for id (1247739947)
% 0.13/0.43  ipcrm: permission denied for id (1247805485)
% 0.20/0.43  ipcrm: permission denied for id (1244725295)
% 0.20/0.43  ipcrm: permission denied for id (1244758064)
% 0.20/0.43  ipcrm: permission denied for id (1244790833)
% 0.20/0.43  ipcrm: permission denied for id (1247871026)
% 0.20/0.43  ipcrm: permission denied for id (1244856371)
% 0.20/0.44  ipcrm: permission denied for id (1247969333)
% 0.20/0.44  ipcrm: permission denied for id (1248002102)
% 0.20/0.44  ipcrm: permission denied for id (1245020216)
% 0.20/0.44  ipcrm: permission denied for id (1245052985)
% 0.20/0.44  ipcrm: permission denied for id (1245085754)
% 0.20/0.44  ipcrm: permission denied for id (1248067643)
% 0.20/0.45  ipcrm: permission denied for id (1245151292)
% 0.20/0.45  ipcrm: permission denied for id (1245184061)
% 0.20/0.45  ipcrm: permission denied for id (1245216830)
% 0.20/0.45  ipcrm: permission denied for id (1248100415)
% 0.20/0.45  ipcrm: permission denied for id (1245282368)
% 0.20/0.45  ipcrm: permission denied for id (1245347906)
% 0.20/0.45  ipcrm: permission denied for id (1245380675)
% 0.20/0.46  ipcrm: permission denied for id (1248165956)
% 0.20/0.46  ipcrm: permission denied for id (1245478982)
% 0.20/0.46  ipcrm: permission denied for id (1248231495)
% 0.20/0.46  ipcrm: permission denied for id (1245544520)
% 0.20/0.46  ipcrm: permission denied for id (1245577289)
% 0.20/0.47  ipcrm: permission denied for id (1248297035)
% 0.20/0.47  ipcrm: permission denied for id (1245642828)
% 0.20/0.47  ipcrm: permission denied for id (1245708366)
% 0.20/0.47  ipcrm: permission denied for id (1245741135)
% 0.20/0.47  ipcrm: permission denied for id (1245806673)
% 0.20/0.47  ipcrm: permission denied for id (1245839442)
% 0.20/0.48  ipcrm: permission denied for id (1248395347)
% 0.20/0.48  ipcrm: permission denied for id (1248428116)
% 0.20/0.48  ipcrm: permission denied for id (1245904981)
% 0.20/0.48  ipcrm: permission denied for id (1245937750)
% 0.20/0.48  ipcrm: permission denied for id (1245970520)
% 0.20/0.48  ipcrm: permission denied for id (1246003289)
% 0.20/0.49  ipcrm: permission denied for id (1248559195)
% 0.20/0.49  ipcrm: permission denied for id (1246101596)
% 0.20/0.49  ipcrm: permission denied for id (1248624734)
% 0.20/0.49  ipcrm: permission denied for id (1246167135)
% 0.20/0.49  ipcrm: permission denied for id (1248657504)
% 0.20/0.49  ipcrm: permission denied for id (1246232673)
% 0.20/0.50  ipcrm: permission denied for id (1246298211)
% 0.20/0.50  ipcrm: permission denied for id (1246330980)
% 0.20/0.50  ipcrm: permission denied for id (1248723045)
% 0.20/0.50  ipcrm: permission denied for id (1248788583)
% 0.20/0.50  ipcrm: permission denied for id (1246429288)
% 0.20/0.50  ipcrm: permission denied for id (1248821353)
% 0.20/0.51  ipcrm: permission denied for id (1246462059)
% 0.20/0.51  ipcrm: permission denied for id (1248886892)
% 0.20/0.51  ipcrm: permission denied for id (1246527597)
% 0.20/0.51  ipcrm: permission denied for id (1246560366)
% 0.20/0.51  ipcrm: permission denied for id (1246593136)
% 0.20/0.51  ipcrm: permission denied for id (1246625905)
% 0.20/0.52  ipcrm: permission denied for id (1246658674)
% 0.20/0.52  ipcrm: permission denied for id (1246756981)
% 0.20/0.52  ipcrm: permission denied for id (1249050742)
% 0.20/0.52  ipcrm: permission denied for id (1249116280)
% 0.20/0.52  ipcrm: permission denied for id (1246855289)
% 0.20/0.53  ipcrm: permission denied for id (1246920827)
% 0.20/0.53  ipcrm: permission denied for id (1249181820)
% 0.20/0.53  ipcrm: permission denied for id (1246986365)
% 0.20/0.53  ipcrm: permission denied for id (1247019134)
% 0.20/0.53  ipcrm: permission denied for id (1247051903)
% 1.13/0.68  % (32461)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.13/0.69  % (32443)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.13/0.70  % (32449)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.13/0.70  % (32442)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.13/0.70  % (32454)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.13/0.70  % (32459)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.13/0.70  % (32436)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.13/0.70  % (32434)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.13/0.70  % (32432)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.13/0.70  % (32443)Refutation not found, incomplete strategy% (32443)------------------------------
% 1.13/0.70  % (32443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.70  % (32442)Refutation not found, incomplete strategy% (32442)------------------------------
% 1.13/0.70  % (32442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.70  % (32455)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.13/0.71  % (32437)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.13/0.71  % (32443)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.71  
% 1.13/0.71  % (32443)Memory used [KB]: 10618
% 1.13/0.71  % (32443)Time elapsed: 0.111 s
% 1.13/0.71  % (32443)------------------------------
% 1.13/0.71  % (32443)------------------------------
% 1.13/0.71  % (32433)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.13/0.71  % (32458)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.13/0.71  % (32442)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.71  
% 1.13/0.71  % (32442)Memory used [KB]: 10618
% 1.13/0.71  % (32442)Time elapsed: 0.107 s
% 1.13/0.71  % (32442)------------------------------
% 1.13/0.71  % (32442)------------------------------
% 1.13/0.71  % (32435)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.13/0.71  % (32456)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.13/0.72  % (32438)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.13/0.72  % (32445)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.13/0.72  % (32436)Refutation not found, incomplete strategy% (32436)------------------------------
% 1.13/0.72  % (32436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.72  % (32450)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.13/0.72  % (32436)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.72  
% 1.13/0.72  % (32436)Memory used [KB]: 6268
% 1.13/0.72  % (32436)Time elapsed: 0.123 s
% 1.13/0.72  % (32436)------------------------------
% 1.13/0.72  % (32436)------------------------------
% 1.13/0.72  % (32449)Refutation not found, incomplete strategy% (32449)------------------------------
% 1.13/0.72  % (32449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.72  % (32449)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.72  
% 1.13/0.72  % (32449)Memory used [KB]: 10618
% 1.13/0.72  % (32449)Time elapsed: 0.138 s
% 1.13/0.72  % (32449)------------------------------
% 1.13/0.72  % (32449)------------------------------
% 1.13/0.72  % (32444)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.13/0.72  % (32451)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.13/0.72  % (32440)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.13/0.72  % (32454)Refutation not found, incomplete strategy% (32454)------------------------------
% 1.13/0.72  % (32454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.72  % (32446)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.13/0.72  % (32437)Refutation found. Thanks to Tanya!
% 1.13/0.72  % SZS status Theorem for theBenchmark
% 1.13/0.72  % SZS output start Proof for theBenchmark
% 1.13/0.72  fof(f280,plain,(
% 1.13/0.72    $false),
% 1.13/0.72    inference(subsumption_resolution,[],[f279,f230])).
% 1.13/0.72  fof(f230,plain,(
% 1.13/0.72    k1_xboole_0 != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))),
% 1.13/0.72    inference(forward_demodulation,[],[f224,f52])).
% 1.13/0.72  fof(f52,plain,(
% 1.13/0.72    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.13/0.72    inference(cnf_transformation,[],[f7])).
% 1.13/0.72  fof(f7,axiom,(
% 1.13/0.72    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.13/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.13/0.72  fof(f224,plain,(
% 1.13/0.72    k2_relat_1(k1_xboole_0) != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))),
% 1.13/0.72    inference(backward_demodulation,[],[f108,f213])).
% 1.13/0.72  fof(f213,plain,(
% 1.13/0.72    k1_xboole_0 = sK2),
% 1.13/0.72    inference(subsumption_resolution,[],[f104,f212])).
% 1.13/0.72  fof(f212,plain,(
% 1.13/0.72    k1_xboole_0 = k1_relat_1(sK2)),
% 1.13/0.72    inference(subsumption_resolution,[],[f211,f100])).
% 1.13/0.72  fof(f100,plain,(
% 1.13/0.72    v1_relat_1(sK2)),
% 1.13/0.72    inference(resolution,[],[f77,f63])).
% 1.13/0.72  fof(f63,plain,(
% 1.13/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.13/0.72    inference(cnf_transformation,[],[f29])).
% 1.13/0.72  fof(f29,plain,(
% 1.13/0.72    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.13/0.72    inference(ennf_transformation,[],[f11])).
% 1.13/0.72  fof(f11,axiom,(
% 1.13/0.72    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.13/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.13/0.72  fof(f77,plain,(
% 1.13/0.72    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.13/0.72    inference(definition_unfolding,[],[f43,f75])).
% 1.13/0.72  fof(f75,plain,(
% 1.13/0.72    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.13/0.72    inference(definition_unfolding,[],[f64,f74])).
% 1.13/0.72  fof(f74,plain,(
% 1.13/0.72    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.13/0.72    inference(definition_unfolding,[],[f71,f72])).
% 1.13/0.72  fof(f72,plain,(
% 1.13/0.72    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.13/0.72    inference(cnf_transformation,[],[f4])).
% 1.13/0.72  fof(f4,axiom,(
% 1.13/0.72    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.13/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.13/0.72  fof(f71,plain,(
% 1.13/0.72    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.13/0.72    inference(cnf_transformation,[],[f3])).
% 1.13/0.72  fof(f3,axiom,(
% 1.13/0.72    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.13/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.13/0.72  fof(f64,plain,(
% 1.13/0.72    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.13/0.72    inference(cnf_transformation,[],[f2])).
% 1.13/0.72  fof(f2,axiom,(
% 1.13/0.72    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.13/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.13/0.72  fof(f43,plain,(
% 1.13/0.72    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.13/0.72    inference(cnf_transformation,[],[f35])).
% 1.13/0.72  fof(f35,plain,(
% 1.13/0.72    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 1.13/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f34])).
% 1.13/0.72  fof(f34,plain,(
% 1.13/0.72    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 1.13/0.72    introduced(choice_axiom,[])).
% 1.13/0.72  % (32457)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.13/0.72  fof(f20,plain,(
% 1.13/0.72    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.13/0.72    inference(flattening,[],[f19])).
% 1.13/0.72  fof(f19,plain,(
% 1.13/0.72    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.13/0.72    inference(ennf_transformation,[],[f17])).
% 1.13/0.72  fof(f17,negated_conjecture,(
% 1.13/0.72    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.13/0.72    inference(negated_conjecture,[],[f16])).
% 1.13/0.72  fof(f16,conjecture,(
% 1.13/0.72    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.13/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).
% 1.13/0.72  fof(f211,plain,(
% 1.13/0.72    ~v1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2)),
% 1.13/0.72    inference(subsumption_resolution,[],[f210,f108])).
% 1.13/0.72  fof(f210,plain,(
% 1.13/0.72    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | ~v1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2)),
% 1.13/0.72    inference(trivial_inequality_removal,[],[f209])).
% 1.13/0.72  fof(f209,plain,(
% 1.13/0.72    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2)),
% 1.13/0.72    inference(resolution,[],[f143,f41])).
% 1.13/0.72  fof(f41,plain,(
% 1.13/0.72    v1_funct_1(sK2)),
% 1.13/0.72    inference(cnf_transformation,[],[f35])).
% 1.13/0.72  fof(f143,plain,(
% 1.13/0.72    ( ! [X4] : (~v1_funct_1(X4) | k2_relat_1(X4) = k2_enumset1(k1_funct_1(X4,sK0),k1_funct_1(X4,sK0),k1_funct_1(X4,sK0),k1_funct_1(X4,sK0)) | k1_relat_1(sK2) != k1_relat_1(X4) | ~v1_relat_1(X4) | k1_xboole_0 = k1_relat_1(sK2)) )),
% 1.13/0.72    inference(superposition,[],[f79,f125])).
% 1.13/0.72  fof(f125,plain,(
% 1.13/0.72    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2)),
% 1.13/0.72    inference(duplicate_literal_removal,[],[f117])).
% 1.13/0.72  fof(f117,plain,(
% 1.13/0.72    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.13/0.72    inference(resolution,[],[f88,f105])).
% 1.13/0.72  fof(f105,plain,(
% 1.13/0.72    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.13/0.72    inference(resolution,[],[f102,f99])).
% 1.13/0.72  fof(f99,plain,(
% 1.13/0.72    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.13/0.72    inference(resolution,[],[f77,f73])).
% 1.13/0.72  fof(f73,plain,(
% 1.13/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.13/0.72    inference(cnf_transformation,[],[f33])).
% 1.13/0.72  fof(f33,plain,(
% 1.13/0.72    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.13/0.72    inference(ennf_transformation,[],[f18])).
% 1.13/0.72  fof(f18,plain,(
% 1.13/0.72    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.13/0.72    inference(pure_predicate_removal,[],[f12])).
% 1.13/0.72  fof(f12,axiom,(
% 1.13/0.72    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.13/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.13/0.72  fof(f102,plain,(
% 1.13/0.72    ( ! [X1] : (~v4_relat_1(sK2,X1) | r1_tarski(k1_relat_1(sK2),X1)) )),
% 1.13/0.72    inference(resolution,[],[f100,f69])).
% 1.13/0.72  fof(f69,plain,(
% 1.13/0.72    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0)) )),
% 1.13/0.72    inference(cnf_transformation,[],[f40])).
% 1.13/0.72  fof(f40,plain,(
% 1.13/0.72    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.13/0.72    inference(nnf_transformation,[],[f32])).
% 1.13/0.72  fof(f32,plain,(
% 1.13/0.72    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.13/0.72    inference(ennf_transformation,[],[f6])).
% 1.13/0.72  fof(f6,axiom,(
% 1.13/0.72    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.13/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.13/0.72  fof(f88,plain,(
% 1.13/0.72    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | k2_enumset1(X0,X0,X1,X2) = X3) )),
% 1.13/0.72    inference(definition_unfolding,[],[f53,f72,f74,f74,f74,f75,f75,f75,f72])).
% 1.13/0.72  fof(f53,plain,(
% 1.13/0.72    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 1.13/0.72    inference(cnf_transformation,[],[f37])).
% 1.13/0.72  fof(f37,plain,(
% 1.13/0.72    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.13/0.72    inference(flattening,[],[f36])).
% 1.13/0.72  fof(f36,plain,(
% 1.13/0.72    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.13/0.72    inference(nnf_transformation,[],[f28])).
% 1.13/0.72  fof(f28,plain,(
% 1.13/0.72    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 1.13/0.72    inference(ennf_transformation,[],[f5])).
% 1.13/0.72  fof(f5,axiom,(
% 1.13/0.72    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 1.13/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 1.13/0.72  fof(f79,plain,(
% 1.13/0.72    ( ! [X0,X1] : (k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.13/0.72    inference(definition_unfolding,[],[f47,f75,f75])).
% 1.13/0.72  fof(f47,plain,(
% 1.13/0.72    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.13/0.72    inference(cnf_transformation,[],[f24])).
% 1.13/0.72  fof(f24,plain,(
% 1.13/0.72    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.13/0.72    inference(flattening,[],[f23])).
% 1.13/0.72  fof(f23,plain,(
% 1.13/0.72    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.13/0.72    inference(ennf_transformation,[],[f9])).
% 1.13/0.72  fof(f9,axiom,(
% 1.13/0.72    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.13/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 1.13/0.72  fof(f104,plain,(
% 1.13/0.72    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.13/0.72    inference(resolution,[],[f100,f49])).
% 1.13/0.72  fof(f49,plain,(
% 1.13/0.72    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.13/0.72    inference(cnf_transformation,[],[f27])).
% 1.13/0.72  fof(f27,plain,(
% 1.13/0.72    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.13/0.72    inference(flattening,[],[f26])).
% 1.13/0.72  fof(f26,plain,(
% 1.13/0.72    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.13/0.72    inference(ennf_transformation,[],[f8])).
% 1.13/0.72  fof(f8,axiom,(
% 1.13/0.72    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.13/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.13/0.72  fof(f108,plain,(
% 1.13/0.72    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)),
% 1.13/0.72    inference(backward_demodulation,[],[f76,f107])).
% 1.13/0.72  fof(f107,plain,(
% 1.13/0.72    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)),
% 1.13/0.72    inference(resolution,[],[f48,f77])).
% 1.13/0.72  fof(f48,plain,(
% 1.13/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.13/0.72    inference(cnf_transformation,[],[f25])).
% 1.13/0.72  fof(f25,plain,(
% 1.13/0.72    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.13/0.72    inference(ennf_transformation,[],[f13])).
% 1.13/0.72  fof(f13,axiom,(
% 1.13/0.72    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.13/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.13/0.72  fof(f76,plain,(
% 1.13/0.72    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 1.13/0.72    inference(definition_unfolding,[],[f45,f75,f75])).
% 1.13/0.72  fof(f45,plain,(
% 1.13/0.72    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 1.13/0.72    inference(cnf_transformation,[],[f35])).
% 1.13/0.72  fof(f279,plain,(
% 1.13/0.72    k1_xboole_0 = k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))),
% 1.13/0.72    inference(forward_demodulation,[],[f278,f52])).
% 1.13/0.72  fof(f278,plain,(
% 1.13/0.72    k2_relat_1(k1_xboole_0) = k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))),
% 1.13/0.72    inference(subsumption_resolution,[],[f277,f221])).
% 1.13/0.72  fof(f221,plain,(
% 1.13/0.72    v1_relat_1(k1_xboole_0)),
% 1.13/0.72    inference(backward_demodulation,[],[f100,f213])).
% 1.13/0.72  fof(f277,plain,(
% 1.13/0.72    k2_relat_1(k1_xboole_0) = k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) | ~v1_relat_1(k1_xboole_0)),
% 1.13/0.72    inference(subsumption_resolution,[],[f276,f51])).
% 1.13/0.72  fof(f51,plain,(
% 1.13/0.72    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.13/0.72    inference(cnf_transformation,[],[f7])).
% 1.13/0.72  fof(f276,plain,(
% 1.13/0.72    k2_relat_1(k1_xboole_0) = k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.13/0.72    inference(resolution,[],[f269,f217])).
% 1.13/0.72  fof(f217,plain,(
% 1.13/0.72    v1_funct_1(k1_xboole_0)),
% 1.13/0.72    inference(backward_demodulation,[],[f41,f213])).
% 1.13/0.72  % (32439)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.13/0.72  fof(f269,plain,(
% 1.13/0.72    ( ! [X4] : (~v1_funct_1(X4) | k2_relat_1(X4) = k2_enumset1(k1_funct_1(X4,sK0),k1_funct_1(X4,sK0),k1_funct_1(X4,sK0),k1_funct_1(X4,sK0)) | k1_xboole_0 != k1_relat_1(X4) | ~v1_relat_1(X4)) )),
% 1.13/0.72    inference(superposition,[],[f79,f245])).
% 1.13/0.72  fof(f245,plain,(
% 1.13/0.72    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.13/0.72    inference(resolution,[],[f235,f66])).
% 1.13/0.72  fof(f66,plain,(
% 1.13/0.72    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.13/0.72    inference(cnf_transformation,[],[f39])).
% 1.13/0.72  fof(f39,plain,(
% 1.13/0.72    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 1.13/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f38])).
% 1.13/0.72  fof(f38,plain,(
% 1.13/0.72    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 1.13/0.72    introduced(choice_axiom,[])).
% 1.13/0.72  fof(f31,plain,(
% 1.13/0.72    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.13/0.72    inference(ennf_transformation,[],[f14])).
% 1.13/0.72  fof(f14,axiom,(
% 1.13/0.72    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.13/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.13/0.72  fof(f235,plain,(
% 1.13/0.72    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.13/0.72    inference(subsumption_resolution,[],[f234,f62])).
% 1.13/0.72  fof(f62,plain,(
% 1.13/0.72    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.13/0.72    inference(cnf_transformation,[],[f1])).
% 1.13/0.72  fof(f1,axiom,(
% 1.13/0.72    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.13/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.13/0.72  fof(f234,plain,(
% 1.13/0.72    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,X0)) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.13/0.72    inference(forward_demodulation,[],[f227,f52])).
% 1.13/0.72  fof(f227,plain,(
% 1.13/0.72    ( ! [X0] : (~r1_tarski(k2_relat_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X0)) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.13/0.72    inference(backward_demodulation,[],[f114,f213])).
% 1.13/0.72  fof(f114,plain,(
% 1.13/0.72    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,X0)) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.13/0.72    inference(resolution,[],[f113,f65])).
% 1.13/0.72  fof(f65,plain,(
% 1.13/0.72    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.13/0.72    inference(cnf_transformation,[],[f30])).
% 1.13/0.72  fof(f30,plain,(
% 1.13/0.72    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.13/0.72    inference(ennf_transformation,[],[f10])).
% 1.13/0.72  fof(f10,axiom,(
% 1.13/0.72    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.13/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.13/0.72  fof(f113,plain,(
% 1.13/0.72    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.13/0.72    inference(forward_demodulation,[],[f112,f107])).
% 1.13/0.72  fof(f112,plain,(
% 1.13/0.72    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))) )),
% 1.13/0.72    inference(subsumption_resolution,[],[f111,f78])).
% 1.13/0.72  fof(f78,plain,(
% 1.13/0.72    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.13/0.72    inference(definition_unfolding,[],[f42,f75])).
% 1.13/0.72  fof(f42,plain,(
% 1.13/0.72    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.13/0.72    inference(cnf_transformation,[],[f35])).
% 1.13/0.72  fof(f111,plain,(
% 1.13/0.72    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))) )),
% 1.13/0.72    inference(subsumption_resolution,[],[f110,f44])).
% 1.13/0.72  fof(f44,plain,(
% 1.13/0.72    k1_xboole_0 != sK1),
% 1.13/0.72    inference(cnf_transformation,[],[f35])).
% 1.13/0.72  fof(f110,plain,(
% 1.13/0.72    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))) )),
% 1.13/0.72    inference(resolution,[],[f109,f77])).
% 1.13/0.72  fof(f109,plain,(
% 1.13/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0 | ~v1_funct_2(sK2,X2,X0) | r2_hidden(k1_funct_1(sK2,X1),k2_relset_1(X2,X0,sK2))) )),
% 1.13/0.72    inference(resolution,[],[f46,f41])).
% 1.13/0.72  fof(f46,plain,(
% 1.13/0.72    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))) )),
% 1.13/0.72    inference(cnf_transformation,[],[f22])).
% 1.13/0.72  fof(f22,plain,(
% 1.13/0.72    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.13/0.72    inference(flattening,[],[f21])).
% 1.13/0.72  fof(f21,plain,(
% 1.13/0.72    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.13/0.72    inference(ennf_transformation,[],[f15])).
% 1.13/0.72  fof(f15,axiom,(
% 1.13/0.72    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.13/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 1.13/0.72  % SZS output end Proof for theBenchmark
% 1.13/0.72  % (32437)------------------------------
% 1.13/0.72  % (32437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.72  % (32437)Termination reason: Refutation
% 1.13/0.72  
% 1.13/0.72  % (32437)Memory used [KB]: 6396
% 1.13/0.72  % (32437)Time elapsed: 0.125 s
% 1.13/0.72  % (32437)------------------------------
% 1.13/0.72  % (32437)------------------------------
% 1.13/0.73  % (32205)Success in time 0.363 s
%------------------------------------------------------------------------------
